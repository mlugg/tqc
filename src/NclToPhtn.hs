{-# LANGUAGE OverloadedStrings, MultiWayIf, LambdaCase, DeriveFunctor #-}

module NclToPhtn where

import Data.Functor
import PhtnSyn
import Data.Text (Text)
import qualified Data.Text as T
import Numeric.Natural
import Data.Map (Map)
import qualified Data.Map as M
import Data.Traversable
import Data.Foldable
import Data.Sequence hiding (zip, length)
import Data.Word
import NclSyn
import Tqc
import Control.Monad
import Data.List (genericLength)

data CompileEnv = CompileEnv
  { envArg   :: Text
  , envFrees :: Map Text Word64
  , envStack :: Map Text Word64
  , envStackOff :: Word64
  }

-- Monad definition and operations {{{

newtype Compile a = Compile { runCompile :: CompileEnv -> Natural -> Tqc (a, [PhtnFunc], PhtnSrc, Natural) }
  deriving (Functor)

instance Applicative Compile where
  pure x = Compile $ \_ n -> pure (x, mempty, mempty, n)
  (<*>) = ap

instance Monad Compile where
  m >>= f = Compile $ \e n0 -> do
    (x, fs0, src0, n1) <- runCompile m e n0
    (y, fs1, src1, n2) <- runCompile (f x) e n1
    pure (y, fs0 <> fs1, src0 <> src1, n2)

instance TqcMonad Compile where
  lift m = Compile $ \_ n -> (\x -> (x, mempty, mempty, n)) <$> m

ask :: Compile CompileEnv
ask = Compile $ \e n -> pure (e, mempty, mempty, n)

asks :: (CompileEnv -> a) -> Compile a
asks f = fmap f ask

tellSrc :: PhtnSrc -> Compile ()
tellSrc src = Compile $ \_ n -> pure ((), mempty, src, n)

flushSrc :: Compile a -> Compile (a, PhtnSrc)
flushSrc m = Compile $ \e n -> f <$> runCompile m e n
  where f (x, fns, src, n) = ((x, src), fns, mempty, n)

flushSrc' :: Compile () -> Compile PhtnSrc
flushSrc' = fmap snd . flushSrc

tellFun :: PhtnFunc -> Compile ()
tellFun fn = Compile $ \_ n -> pure ((), pure fn, mempty, n)

freshId :: Compile Natural
freshId = Compile $ \_ n -> pure (n, mempty, mempty, n+1)

withEnv :: (CompileEnv -> CompileEnv) -> Compile a -> Compile a
withEnv f m = Compile $ runCompile m . f

-- }}}

lookupVar :: Text -> Compile ()
lookupVar x = do
  e <- ask
  if
    | x == envArg e -> tellSrc $ pure PPushArg
    | Just i <- M.lookup x (envStack e) -> tellSrc $ pure $ PPushStack (BottomOff i)
    | Just i <- M.lookup x (envFrees e) -> tellSrc $ pure $ PPushClos i
    | otherwise -> throwErr _ -- TODO: global name

withStack :: Map Text Word64 -> Compile a -> Compile a
withStack new = withEnv $ \e -> e { envStack = new <> envStack e, envStackOff = fromIntegral (M.size new) + envStackOff e }

withStack' :: [Text] -> Compile a -> Compile a
withStack' ns m = do
  off <- asks envStackOff
  withStack (M.fromList $ zip ns [off..]) m

withStackOff :: Word64 -> Compile a -> Compile a
withStackOff extra = withEnv $ \e -> e { envStackOff = extra + envStackOff e }

compile :: Expr -> Compile ()
compile = \case
  EName x -> lookupVar x

  ENatLit x -> do
    when (x > fromIntegral (maxBound :: Word64)) $ throwErr NumRangeErr

    tellSrc $ PAllocate (AllocData 0)
           <| PObjSetLit (TopOff 0) 0 (fromIntegral x)
           <| mempty

  EAppl e0 e1 -> do
    tellSrc $ pure $ PAllocate AllocThunk
    withStackOff 1 $ compile e0
    withStackOff 2 $ compile e1
    tellSrc $ PObjSetPtr (TopOff 2) 0 (TopOff 1) -- fn
           <| PObjSetPtr (TopOff 2) 1 (TopOff 0) -- arg
           <| PPop 2
           <| mempty

  ELambda arg frees body -> do
    fnName <- mappend "fn_" . T.pack . show <$> freshId

    let frees' = zip frees [0..]
        nfrees = fromIntegral $ length frees'
        fnEnv = CompileEnv arg (M.fromList frees') M.empty 0

    cbody <- flushSrc' $ withEnv (const fnEnv) $ compile body
    tellFun $ PhtnFunc fnName cbody

    tellSrc $ pure $ PAllocate (AllocFun nfrees fnName)

    for_ frees' $ \(name, idx) -> do
      lookupVar name
      tellSrc $ PObjSetPtr (TopOff 1) (idx + 1) (TopOff 0)
             <| PPop 1
             <| mempty

  ELet bs body -> do
    -- Allocate an indirection for each binding
    tellSrc $ fromList $ PAllocate AllocInd <$ bs

    sOff <- asks envStackOff

    let bindName (Binding n _) = n
        names = bindName <$> bs
        stackNew = M.fromList $ zip names [sOff..]
        nbinds = fromIntegral $ M.size stackNew

    withStack stackNew $ do
      for_ bs $ \(Binding name expr) -> do
        -- Compile the definition
        compile expr

        -- Stack now contains ptr to real value; we need to update the
        -- indirection

        -- Find location of indirection on stack
        let indLoc = stackNew M.! name

        -- Set ptr in indirection, and pop the compiled val off the
        -- stack
        tellSrc $ PObjSetPtr (BottomOff indLoc) 0 (TopOff 0)
               <| PPop 1
               <| mempty

      compile body

    tellSrc $ PReplaceStack (BottomOff sOff) (TopOff 0) -- move the resulting value down to where our return value needs to be
           <| PPop nbinds -- Pop the original return value plus (n-1) binds (the last one remains, it's been replaced with the ret val)
           <| mempty

  ECase scrut name alts def -> do
    -- Evaluate the scrutinee
    compile scrut

    -- Force eval
    tellSrc $ pure PEval

    withStack' [name] $ do
      -- Create a list of switch alternatives
      altsSrcs <- traverse compileCase alts
      -- Compile the default case
      defSrc <- flushSrc' $ compile def
      -- Switch on its constructor
      tellSrc $ pure $ PObjSwitchLit 0 altsSrcs defSrc

compileCase :: Alt -> Compile SwitchAlt
compileCase (Alt pat expr) = do
  (constrId, binds) <- case pat of
    PConstr name binds ->
      lookupConstrId name <&> \i ->
      (i, binds)
    PNatLit x ->
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

lookupConstrId :: Text -> Compile Word64
lookupConstrId = _
