{-# LANGUAGE Safe, LambdaCase, DataKinds, DeriveFunctor, OverloadedStrings #-}

module Rename where

import Tqc
import QntSyn
import Data.Text (Text)
import Data.Set (Set)
import qualified Data.Set as S
import Control.Monad
import Data.Traversable
import Common

newtype Rename a = Rename { runRename :: Set Text -> Tqc a }
  deriving (Functor)

instance Applicative Rename where
  pure x = Rename $ \_ -> pure x
  (<*>) = ap

instance Monad Rename where
  m >>= f = Rename $ \locs -> do
    x <- runRename m locs
    runRename (f x) locs

instance TqcMonad Rename where
  lift m = Rename $ \_ -> m

lookupLocal :: Text -> Rename Bool
lookupLocal x = Rename $ \locs -> pure $ x `S.member` locs

withLocals :: Set Text -> Rename a -> Rename a
withLocals new m = Rename $ \locs -> runRename m (new <> locs)

withLocal :: Text -> Rename a -> Rename a
withLocal = withLocals . S.singleton

renameExpr :: QntExpr 'Parsed -> Rename (QntExpr 'Renamed)
renameExpr = \case
  QntVar n -> do
    isLocal <- lookupLocal n
    if isLocal
    then pure $ QntVar (LoclName $ SrcName n)
    else findQualified n >>= \case
      Nothing -> throwErr _ -- TODO XXX
      Just m  -> pure $ QntVar (QualName (Qual m n))

  QntLet bs body ->
    let names = S.fromList $ bindName <$> bs
    in withLocals names $ do
      bs' <- for bs $ \b ->
        case b of
          QntImpl n e   -> QntImpl n <$> renameLExpr e
          QntExpl n e s -> QntExpl n <$> renameLExpr e <*> renameLScheme s

      body' <- renameLExpr body

      pure $ QntLet bs' body'

  QntCase e as ->
    QntCase
    <$> renameLExpr e
    <*> traverse renameLAlt as

  QntNatLit x -> pure $ QntNatLit x

  QntApp e0 e1 ->
    QntApp
    <$> renameLExpr e0
    <*> renameLExpr e1

  QntLam x e -> withLocal x $
    QntLam x <$> renameLExpr e

renameLExpr :: LQntExpr 'Parsed -> Rename (LQntExpr 'Renamed)
renameLExpr = traverse renameExpr

renameAlt :: QntAlt 'Parsed -> Rename (QntAlt 'Renamed)
renameAlt (QntAlt p e) =
  let ns = findPatNames p
  in withLocals ns $ QntAlt <$> renamePat p <*> renameLExpr e
  where
    findPatNames = \case
      QntNamePat x -> S.singleton x
      QntNatLitPat _ -> S.empty
      QntConstrPat _ ps -> foldMap findPatNames ps

renamePat :: QntPat 'Parsed -> Rename (QntPat 'Renamed)
renamePat = \case
  QntNamePat b -> pure $ QntNamePat b
  QntNatLitPat x -> pure $ QntNatLitPat x
  QntConstrPat c ps ->
    findConstr c >>= \case
      Nothing -> throwErr _ -- TODO XXX
      Just m  -> QntConstrPat (Qual m c) <$> traverse renamePat ps

renameLAlt :: LQntAlt 'Parsed -> Rename (LQntAlt 'Renamed)
renameLAlt = traverse renameAlt

renameScheme :: Scheme Text -> Rename (Scheme Qual)
renameScheme (Scheme vs t) = Scheme vs <$> renameType t

renameLScheme :: LScheme Text -> Rename (LScheme Qual)
renameLScheme = traverse renameScheme

renameType :: Type Text -> Rename (Type Qual)
renameType = \case
  TName n -> findQualifiedType n >>= \case
               Nothing -> throwErr _
               Just m  -> pure $ TName (Qual m n)
  TVar v     -> pure $ TVar v
  TApp t0 t1 -> TApp <$> renameType t0 <*> renameType t1

findQualified :: Text -> Rename (Maybe Module)
findQualified x = pure $ Just $ Module ["Foo", "Bar"] -- XXX TODO

findQualifiedType :: Text -> Rename (Maybe Module)
findQualifiedType x = pure $ Just $ Module ["Foo", "Bar"] -- XXX TODO

findConstr :: Text -> Rename (Maybe Module)
findConstr x = pure $ Just $ Module ["Baz", "Faz"] -- XXX TODO
