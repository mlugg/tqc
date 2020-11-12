{-# LANGUAGE DeriveFunctor #-}

module Tqc where

import Data.Sequence
import Control.Monad

data CompileError
  = NumRangeErr
  deriving (Show)

data CompileWarning
  = Warn_TMP
  deriving (Show)

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
