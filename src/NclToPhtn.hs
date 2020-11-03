{-# LANGUAGE OverloadedStrings, MultiWayIf, LambdaCase, GeneralizedNewtypeDeriving #-}

module NclToPhtn where

import PhtnSyn
import Data.Text (Text)
import qualified Data.Text as T
import Numeric.Natural
import Data.Map (Map)
import qualified Data.Map as M
import Data.Traversable
import Data.Word
import NclSyn
import Control.Monad.RWS
import Control.Monad.Except

data CompileEnv = CompileEnv
  { envArg   :: Text
  , envFrees :: Map Text Word64
  , envStack :: Map Text Word64
  , envStackOff :: Word64
  }

data CodeGenError = NameError Text | OtherError
  deriving (Show)

newtype Compile a = Compile { unCompile :: RWST CompileEnv [PhtnFunc] Natural (Except CodeGenError) a }
  deriving
    ( Functor
    , Applicative
    , Monad
    , MonadReader CompileEnv
    , MonadState Natural
    , MonadWriter [PhtnFunc]
    , MonadError CodeGenError
    )

-- rax: Function argument
-- rbx: Pointer to function object
-- rcx: Return value
-- rdx: Intermediate computation result

freshID :: Compile Natural
freshID = get >>= \x -> x <$ put (x+1)

lookupVar :: Text -> Compile [PhtnInsn]
lookupVar x = do
  e <- ask
  if
    | x == envArg e -> pure [ FPushArg ]
    | Just i <- M.lookup x (envStack e) -> pure [ FPushStack i ]
    | Just i <- M.lookup x (envFrees e) -> pure [ FPushBody i ]
    | otherwise -> throwError $ NameError x -- This issue should have been caught in type checking; this indicates a compiler bug!

runCompile :: Compile a -> CompileEnv -> Natural -> Either CodeGenError (a, Natural, [PhtnFunc])
runCompile m e s = runExcept $ runRWST (unCompile m) e s

withStack :: Map Text Word64 -> Compile a -> Compile a
withStack new = local $ \e -> e { envStack = new <> envStack e }

withStackOff :: Word64 -> Compile a -> Compile a
withStackOff extra = local $ \e -> e { envStackOff = extra + envStackOff e }

compile :: Expr -> Compile [PhtnInsn]
compile = \case
  EName x -> lookupVar x

  ENatLit x -> do
    when (x > fromIntegral (maxBound :: Word64)) $ throwError OtherError

    pure
      [ FAllocate $ AllocData 0
      , FObjSetLit (TopOff 0) 0 (fromIntegral x)
      ]

  EAppl e0 e1 -> do
    s0 <- compile e0
    s1 <- withStackOff 1 $ compile e1
    pure $
      [ FAllocate AllocThunk ]
      <> s0 <> s1 <>
      [ FObjSetPtr (TopOff 2) 0 (TopOff 1) -- fn
      , FObjSetPtr (TopOff 2) 1 (TopOff 0) -- arg
      , FPop 2
      ]

  ELambda arg frees body -> do
    fnName <- mappend "fn_" . T.pack . show <$> freshID

    let frees' = zip frees [0..]
        nfrees = fromIntegral $ length frees'
        fnEnv = CompileEnv arg (M.fromList frees') M.empty 0

    cbody <- local (const fnEnv) $ compile body
    tell [ PhtnFunc fnName cbody ]

    let src0 = [ FAllocate $ AllocFun nfrees fnName ]

    src1 <- fmap concat $ for frees' $ \(name, idx) -> do
      getVal <- lookupVar name
      pure $ getVal <>
        [ FObjSetPtr (TopOff 1) idx (TopOff 0)
        , FPop 1
        ]

    pure $ src0 <> src1

  ELet bs body -> do
    -- Get the current stack offset
    sOff <- asks envStackOff
    -- Allocate an indirection for each binding
    let src0 = FAllocate AllocInd <$ bs
    -- Create an environment including all of these indirections from
    -- the stack
    let stackNew = M.fromList $ zip (fst <$> bs) [sOff..]
        nbinds = fromIntegral $ M.size stackNew

    src1 <- fmap concat $
      withStackOff nbinds $
      withStack stackNew $
      for bs $ \(name,expr) -> do
        -- Compile the definition
        s <- compile expr

        -- Stack now contains ptr to real value; we need to update the
        -- indirection

        -- Find location of indirection on stack
        let indLoc = stackNew M.! name

        -- Set ptr in indirection, and pop the compiled val off the
        -- stack
        pure $ s <>
          [ FObjSetPtr (BottomOff indLoc) 0 (TopOff 0)
          ]

    src2 <- withStackOff nbinds $ withStack stackNew $ compile body

    let src3 = 
          [ FReplaceStack (BottomOff sOff) (TopOff 0) -- move the resulting value down to where our return value needs to be
          , FPop nbinds -- Pop the original return value plus (n-1) binds (the last one remains, it's been replaced with the ret val)
          ]

    pure $ src0 <> src1 <> src2 <> src3

  ECase scrut ps def -> _

