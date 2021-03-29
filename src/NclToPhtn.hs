{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}

module NclToPhtn where

import Common
import Data.Functor
import PhtnSyn
import Data.Text (Text)
import qualified Data.Text as T
import Numeric.Natural
import Data.Map (Map)
import qualified Data.Map as M
import Data.Foldable
import Data.Traversable
import Data.Sequence hiding (zip, length)
import Data.Word
import NclSyn
import Tqc
import Control.Monad
import Data.List (genericLength)

data CompileEnv = CompileEnv
  { envArg   :: Maybe NclBinder -- The name of the current function's argument
  , envFrees :: Map NclBinder Word64 -- A map from binders to function closure offsets
  , envStack :: Map NclBinder Word64 -- A map from binders to stack offsets
  , envStackOff :: Word64 -- The current size of the stack frame
  } deriving (Show)

-- Monad definition and operations {{{

newtype Compile a = Compile { runCompile :: Map Qual Word64 -> CompileEnv -> Natural -> Tqc (a, [PhtnFunc], PhtnSrc, Natural) }
  deriving (Functor)

runCompile' :: Map Qual Word64 -> Compile a -> Tqc (a, [PhtnFunc])
runCompile' constrEnv m = do
  (x, fs, _, _) <- runCompile m constrEnv (CompileEnv Nothing mempty mempty 0) 0
  pure (x, fs)

instance Applicative Compile where
  pure x = Compile $ \ _ _ n -> pure (x, mempty, mempty, n)
  (<*>) = ap

instance Monad Compile where
  m >>= f = Compile $ \ ce e n0 -> do
    (x, fs0, src0, n1) <- runCompile m ce e n0
    (y, fs1, src1, n2) <- runCompile (f x) ce e n1
    pure (y, fs0 <> fs1, src0 <> src1, n2)

instance TqcMonad Compile where
  lift m = Compile $ \ _ _ n -> (\x -> (x, mempty, mempty, n)) <$> m

ask :: Compile CompileEnv
ask = Compile $ \ _ e n -> pure (e, mempty, mempty, n)

asks :: (CompileEnv -> a) -> Compile a
asks f = fmap f ask

tellSrc :: PhtnSrc -> Compile ()
tellSrc src = Compile $ \ _ _ n -> pure ((), mempty, src, n)

flushSrc :: Compile a -> Compile (a, PhtnSrc)
flushSrc m = Compile $ \ ce e n -> f <$> runCompile m ce e n
  where f (x, fns, src, n) = ((x, src), fns, mempty, n)

flushSrc' :: Compile () -> Compile PhtnSrc
flushSrc' = fmap snd . flushSrc

tellFun :: PhtnFunc -> Compile ()
tellFun fn = Compile $ \ _ _ n -> pure ((), pure fn, mempty, n)

freshId :: Compile Natural
freshId = Compile $ \ _ _ n -> pure (n, mempty, mempty, n+1)

withEnv :: (CompileEnv -> CompileEnv) -> Compile a -> Compile a
withEnv f m = Compile $ \ ce e n -> runCompile m ce (f e) n

-- }}}

-- Given a resolved name, looks up a variable and pushes it to the
-- stack. Throws an error if the variable is not in scope.
lookupVar :: RName -> Compile ()
lookupVar = \case
  -- If we're referring to a global, simply refer to it by name - e.g.
  -- 'Data.Nat.add' is named 'obj_Data.Nat.add' in the binary.
  QualName q -> tellSrc $ pure $
    PPushGlobl (qualToAsmName q)

  -- If we're referring to a local, look it up separately.
  LoclName x -> lookupLocal (NclBinder x)

-- Looks up a local variable in the current scope. If in scope, the
-- variable is pushed; otherwise, an error is thrown.
lookupLocal :: NclBinder -> Compile ()
lookupLocal x@(NclBinder lname) = do
    -- Get the current compilation environment
    e <- ask
    if -- Is the value the current function argument?
       | Just x == envArg e -> tellSrc $ pure PPushArg
       -- Is it on the stack from a let-binding?
       | Just i <- M.lookup x (envStack e) -> tellSrc $ pure $ PPushStack (BottomOff i)
       -- Is it a free variable, i.e. in the current function's closure?
       | Just i <- M.lookup x (envFrees e) -> tellSrc $ pure $ PPushClos i
       -- The variable is unknown; this should have been caught earlier,
       -- but we'll throw it now anyway
       | otherwise -> throwErr $ TypeErr $ TeUnknownVar (LoclName lname)

-- Extends the stack with the given variable binders at the given
-- offsets, and runs an action with this extended stack
withStack :: Map NclBinder Word64 -> Compile a -> Compile a
withStack new = withEnv $ \e ->
  e { envStack = new <> envStack e
    , envStackOff = fromIntegral (M.size new) + envStackOff e
    }

-- Extends the stack with a sequence of variables which are assumed to
-- have been added at the top of the stack
withStack' :: [NclBinder] -> Compile a -> Compile a
withStack' ns m = do
  off <- asks envStackOff
  withStack (M.fromList $ zip ns [off..]) m

-- Runs an action with an increased stack offset
withStackOff :: Word64 -> Compile a -> Compile a
withStackOff extra = withEnv $ \e -> e { envStackOff = extra + envStackOff e }

-- Compiles a Nucleus expression to Photon instructions
compile :: NclExpr -> Compile ()
compile = \case
  NclVar x -> lookupVar x

  NclNatLit x -> do
    -- Check the literal is in the range that can be safely represented
    when (x > fromIntegral (maxBound :: Word64)) $ throwErr NumRangeErr

    -- Allocate a data constructor with a body length of 0, and set the
    -- first field within it (i.e. the actual value) to the value of the
    -- literal
    tellSrc $ PAllocate (AllocData 0)
           <| PObjSetLit (TopOff 0) 0 (fromIntegral x)
           <| mempty

  NclApp e0 e1 -> do
    -- Allocate a unary thunk for the application
    tellSrc $ pure $ PAllocate AllocThunk1

    -- Compile the two sub-expressions (with the correct stack offsets)
    withStackOff 1 $ compile e0
    withStackOff 2 $ compile e1

    tellSrc $ PObjSetPtr (TopOff 2) 0 (TopOff 1) -- First field of thunk is the function object
           <| PObjSetPtr (TopOff 2) 1 (TopOff 0) -- Second field of thunk is the arg object
           <| PPop 2 -- Pop the sub-expressions from the stack
           <| mempty

  NclLam arg frees body -> do
    -- Give the function containing the lambda's code a unique name
    fnName <- mappend "fn_" . T.pack . show <$> freshId

    let -- Associate every free variable in the lambda expression with an ID
        frees' = zip frees [0..]
        -- Count the number of free variables
        nfrees = fromIntegral $ length frees'
        -- Create a new compilation environment for compiling the lambda
        -- body; replacing the argument name, the list of free
        -- variables (with frees'), the stack variables (there are none
        -- as it's a new stack frame), and the stack offset (zero as
        -- it's a new stack frame)
        fnEnv = CompileEnv (Just arg) (M.fromList frees') M.empty 0

    -- Compile the body expression with the environment created above,
    -- and extract all the source code it writes
    cbody <- flushSrc' $ withEnv (const fnEnv) $ compile body

    -- Output a complete function containing the lambda's body code with
    -- the given name
    tellFun $ PhtnFunc fnName cbody

    -- Output a source line that allocates a function *object* which
    -- refers to the code written above and has a sufficiently sized
    -- closure
    tellSrc $ pure $ PAllocate (AllocFun nfrees fnName)

    -- Iterate over each name/index pair in the closure
    for_ frees' $ \(name, idx) -> do
      -- Lookup the value within the *current* scope, and push it to the
      -- stack
      lookupLocal name
      -- Set the field within the object's closure, and pop the value
      -- back off of the stack
      tellSrc $ PObjSetPtr (TopOff 1) (idx + 1) (TopOff 0)
             <| PPop 1
             <| mempty

  NclLet bs body -> do
    -- We can't immediately fill the closures, as bindings may be mutually
    -- recursive. Instead, we construct the thunks, then iterate over
    -- all their closures and fill them correctly

    -- Iterate over every bind, with free variables 'frees' and body
    -- expression 'bindBody'
    closures <- for bs $ \(NclBind _ frees bindBody) -> do
      -- Let-bindings introduce laziness by constructing nullary thunks
      -- around the bound expressions. Create a unique name for the
      -- function; the 'nfn' prefix stands for "nullary function".
      fnName <- mappend "nfn_" . T.pack . show <$> freshId

      let -- Associate every free variable in the binding body with an ID
          frees' = zip frees [0..]
          -- Count the number of free variables
          nfrees = fromIntegral $ length frees
          -- Create a new compilation environment for the nullary
          -- thunk's code; replacing the argument name (there is none),
          -- the list of free variables (with frees'), and the stack
          -- variables/offset (reset since it's a new stack frame)
          fnEnv = CompileEnv Nothing (M.fromList frees') M.empty 0

      -- Compile the right-hand side of the binding within the given
      -- environment, and extract the written source code.
      cbody <- flushSrc' $ withEnv (const fnEnv) $ compile bindBody

      -- Output a function with the generated name and code
      tellFun $ PhtnFunc fnName cbody

      -- Output a source line that allocates a nullary thunk with the
      -- correct number of frees and the given function name
      tellSrc $ pure $ PAllocate (AllocThunk0 nfrees fnName)

      -- Return the set of free variables
      pure frees'


    -- 'closures' is of type '[ [(NclBinder, Int)] ]'. Each inner list
    -- represents a binding's closure; specifically, associations
    -- between a referenced variable and the offset in the thunk object
    -- it should appear at.

    let nbinds = fromIntegral $ length bs

    let closures' = zip [nbinds, nbinds-1 ..] closures

    sOff <- asks envStackOff

    let names = nclBinder <$> bs
        stackNew = M.fromList $ zip names [sOff..]

    withStack stackNew $ do
      for_ closures' $ \(off, frees) ->
        for_ frees $ \(name, idx) -> do
          lookupLocal name
          tellSrc $ PObjSetPtr (TopOff off) (idx + 1) (TopOff 0)
                 <| PPop 1
                 <| mempty

      compile body

    tellSrc $ PReplaceStack (BottomOff sOff) (TopOff 0) -- Move the resulting value down to where our return value needs to be
           <| PPop nbinds -- Pop the original return value plus (n-1) binds (the last one remains, it's been replaced with the return val)
           <| mempty

  NclCase scrut alts def -> do
    -- Evaluate the scrutinee
    compile (NclVar scrut)

    -- Force evaluation to WHNF
    tellSrc $ pure PEval

    -- We don't compile this with a stack offset, because when the code
    -- is run (in the PObjSwitchLit body) the object has actually been
    -- removed from the stack.

    -- Create a list of switch alternatives
    altsSrcs <- traverse compileCase alts
    -- Compile the default case
    defSrc <- flushSrc' $ compile def
    -- Switch on its constructor
    tellSrc $ pure $ PObjSwitchLit 0 altsSrcs defSrc

compileCase :: NclAlt -> Compile SwitchAlt
compileCase (NclAlt pat expr) = do
  (constrId, binds) <- case pat of
    NclConstrPat name binds ->
      lookupConstr name <&> \i ->
      (i, binds)
    NclNatLitPat x ->
      if x > fromIntegral (maxBound :: Word64)
      then throwErr NumRangeErr
      else pure (fromIntegral x, [])

  let nbinds = genericLength binds

  src <- flushSrc' $ do
    sOff <- asks envStackOff
    tellSrc $ fromList $ PObjGetPtr (BottomOff sOff) <$> [1..nbinds]
    withStack' binds $ compile expr
    tellSrc $ PReplaceStack (BottomOff sOff) (TopOff 0)
           <| PPop nbinds
           <| mempty

  pure $ SwitchAlt constrId src

lookupConstr :: Qual -> Compile Word64
lookupConstr c = Compile $ \ ce _ n -> case M.lookup c ce of
  Nothing -> throwErr $ TypeErr $ TeUnknownVar $ QualName c -- This should have been caught earlier, but we'll throw it now anyway
  Just x  -> pure (x, mempty, mempty, n)

compileTopLevelBind :: NclBind -> Compile (Text, Text)
compileTopLevelBind (NclBind (NclBinder name) _ expr) = do
    -- Give the function containing the bind's code a unique name
    fnName <- mappend "fn_" . T.pack . show <$> freshId

    -- Compile the body expression and extract all the source code it writes
    cexpr <- flushSrc' $ compile expr

    -- Output a complete function containing the lambda's body code with
    -- the given name
    tellFun $ PhtnFunc fnName cexpr

    let name' = case name of
          SrcName x -> x
          GenName x -> x

    -- Return the binding name and compiled function name
    pure (name', fnName)

compileConstrFunction :: Qual -> Int -> Compile (Text, Text)
compileConstrFunction constr@(Qual _ name) nargs = do
  fnName <- mappend "cfn_" . T.pack . show <$> freshId
  helperFn <- flushSrc' $ go 0
  tellFun $ PhtnFunc fnName helperFn
  pure (name, fnName)
  where nargs' = fromIntegral nargs
        go argsTaken
          | argsTaken == nargs' = do
              constrId <- lookupConstr constr
              tellSrc $ PAllocate (AllocData nargs')
                     <| PObjSetLit (TopOff 0) 0 constrId
                     <| mempty

          | otherwise = do
              fnName <- mappend "cfn_" . T.pack . show <$> freshId

              body <- flushSrc' $ do
                go (argsTaken + 1)

                when (argsTaken > 0) $
                  for_ [0 .. argsTaken - 1] $ \ n ->
                    tellSrc $ PPushClos n
                           <| PObjSetPtr (TopOff 1) (n + 1) (TopOff 0)
                           <| PPop 1
                           <| mempty

                tellSrc $ PPushArg
                       <| PObjSetPtr (TopOff 1) (argsTaken + 1) (TopOff 0)
                       <| PPop 1
                       <| mempty

              tellFun $ PhtnFunc fnName body
              tellSrc $ pure $ PAllocate (AllocFun argsTaken fnName)
