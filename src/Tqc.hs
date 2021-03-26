{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE LambdaCase #-}

module Tqc where

import Common
import Control.Monad
import Control.Monad.IO.Class
import QntSyn
import Data.Text (Text)
import Text.Megaparsec (ParseErrorBundle)
import Data.Void

data TypeError
  = TeInExpr (LQntExpr 'Renamed) TypeError
  | TeInScheme (LScheme Qual) TypeError
  | TeSchemeMismatch (Scheme Qual) (Scheme Qual)
  | TeTypeMismatch (Type Qual) (Type Qual)
  | TeInfiniteType (Type Qual) (Type Qual)
  | TeKindNotStar
  | TeBadTypeApp (Type Qual) Kind (Type Qual) Kind
  | TeUnknownVar RName
  | TeUnknownType Qual
  | TeBadPatternArgs Qual Int Int

data CompileError
  = NumRangeErr
  | TypeErr TypeError
  | UnknownVarErr Text
  | UnknownTypeErr Text
  | AmbiguousNameErr Text [Qual]
  | ParseErr (ParseErrorBundle Text Void)
  | NasmErr FilePath
  | LinkErr FilePath

data QuantaFile = QuantaFile
  { qntSrcName :: FilePath
  , qntAsmName :: FilePath
  , qntObjName :: Maybe FilePath
  } deriving (Show)

data TqcConfig = TqcConfig
  { tqcShared     :: Bool
  , tqcOptLevel   :: Int
  , tqcFiles      :: [QuantaFile]
  , tqcBinaryFile :: Maybe FilePath
  } deriving (Show)

-- TQC: Tiny Quanta Compiler
class TqcMonad m where
  askConf  :: m TqcConfig
  throwErr :: CompileError -> m a

  lift :: Tqc a -> m a

  askConf = lift askConf
  throwErr e = lift $ throwErr e

newtype Tqc a = Tqc { runTqc :: TqcConfig -> IO (Either CompileError a) }
  deriving (Functor)

instance Applicative Tqc where
  pure x = Tqc $ \ _ -> pure $ Right x
  (<*>) = ap

instance Monad Tqc where
  m >>= f = Tqc $ \ cfg ->
    runTqc m cfg >>= \ case
      Left err -> pure $ Left err
      Right x -> runTqc (f x) cfg

instance TqcMonad Tqc where
  askConf = Tqc $ \ c -> pure $ Right c
  throwErr e = Tqc $ \ _ -> pure $ Left e
  lift = id

instance MonadIO Tqc where
  liftIO m = Tqc $ \ _ -> Right <$> m

tqcCatchErr :: Tqc a -> (CompileError -> Tqc a) -> Tqc a
tqcCatchErr m f = Tqc $ \ cfg -> runTqc m cfg >>= \ case
  Left err -> runTqc (f err) cfg
  Right x  -> pure $ Right x
