{-# LANGUAGE DeriveFunctor, DataKinds #-}

module Tqc where

import Common
import Data.Sequence
import Control.Monad
import QntSyn

data TypeError
  = TeInExpr (QntExpr 'Renamed) TypeError
  | TeInScheme (Scheme RName) TypeError

data CompileError
  = NumRangeErr
  | TypeErr TypeError

data CompileWarning
  = Warn_TMP

data TqcConfig = TqcConfig {}

-- TQC: Tiny Quanta Compiler
class TqcMonad m where
  askConf  :: m TqcConfig
  throwErr :: CompileError -> m a
  logWarn  :: CompileWarning -> m ()

  lift :: Tqc a -> m a

  askConf = lift askConf
  throwErr e = lift $ throwErr e
  logWarn w = lift $ logWarn w

newtype Tqc a = Tqc { runTqc :: TqcConfig -> Either CompileError (a, Seq CompileWarning) }
  deriving (Functor)

instance Applicative Tqc where
  pure x = Tqc $ \_ -> Right (x, mempty)
  (<*>) = ap

instance Monad Tqc where
  m >>= f = Tqc $ \c -> do
    (x,ws0) <- runTqc m c
    (y,ws1) <- runTqc (f x) c
    pure $ (y, ws0 <> ws1)

instance TqcMonad Tqc where
  askConf = Tqc $ \c -> pure (c, mempty)
  throwErr e = Tqc $ \_ -> Left e
  logWarn w = Tqc $ \_ -> Right ((), pure w)
  lift = id

tqcCatchErr :: Tqc a -> (CompileError -> Tqc a) -> Tqc a
tqcCatchErr m f = Tqc $ \conf -> case runTqc m conf of
  Left err -> runTqc (f err) conf
  Right x  -> Right x
