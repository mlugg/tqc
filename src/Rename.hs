{-# LANGUAGE Safe, LambdaCase, DataKinds, DeriveFunctor, OverloadedStrings #-}

module Rename where

import Tqc
import QntSyn
import Data.Text (Text)
import Data.Set (Set)
import qualified Data.Set as S
import Control.Monad
import Common

newtype Rename a = Rename { runRename :: [Qual] -> [Qual] -> Set Text -> Tqc a }
  deriving (Functor)

runRename' :: [Qual] -> [Qual] -> Rename a -> Tqc a
runRename' vs ts m = runRename m vs ts mempty

instance Applicative Rename where
  pure x = Rename $ \ _ _ _ -> pure x
  (<*>) = ap

instance Monad Rename where
  m >>= f = Rename $ \ vals types locs -> do
    x <- runRename m vals types locs
    runRename (f x) vals types locs

instance TqcMonad Rename where
  lift m = Rename $ \ _ _ _ -> m

lookupLocal :: Text -> Rename Bool
lookupLocal x = Rename $ \ _ _ locs -> pure $ x `S.member` locs

withLocals :: Set Text -> Rename a -> Rename a
withLocals new m = Rename $ \ vals types locs -> runRename m vals types (new <> locs)

withLocal :: Text -> Rename a -> Rename a
withLocal = withLocals . S.singleton

findQualified :: Text -> Rename (Maybe Module)
findQualified x = Rename $ \ vals _ _ ->
  let matches = filter (\ (Qual _ y) -> x == y) vals
  in case matches of
    [Qual m _] -> pure $ Just m
    []         -> pure $ Nothing
    _          -> throwErr $ AmbiguousNameErr x matches

findQualifiedType :: Text -> Rename (Maybe Module)
findQualifiedType x = Rename $ \ _ types _ ->
  let matches = filter (\ (Qual _ y) -> x == y) types
  in case matches of
    [Qual m _] -> pure $ Just m
    []         -> pure $ Nothing
    _          -> throwErr $ AmbiguousNameErr x matches

renameExpr :: QntExpr 'Parsed -> Rename (QntExpr 'Renamed)
renameExpr = \case
  QntVar n -> do
    isLocal <- lookupLocal n
    if isLocal
    then pure $ QntVar (LoclName $ SrcName n)
    else findQualified n >>= \case
      Nothing -> throwErr $ UnknownVarErr n
      Just m  -> pure $ QntVar (QualName (Qual m n))

  QntLet bs body ->
    let names = S.fromList $ bindName <$> bs
    in withLocals names $ do
      bs' <- traverse renameBind bs
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
      QntNamePat (NamePat x) -> S.singleton x
      QntNatLitPat _ -> S.empty
      QntConstrPat (ConstrPat _ ps) -> foldMap findPatNames ps

renamePat :: QntPat 'Parsed -> Rename (QntPat 'Renamed)
renamePat = \case
  QntNamePat (NamePat b) -> pure $ QntNamePat (NamePat b)
  QntNatLitPat (NatLitPat x) -> pure $ QntNatLitPat (NatLitPat x)
  QntConstrPat (ConstrPat c ps) ->
    findQualified c >>= \case
      Nothing -> throwErr $ UnknownVarErr c
      Just m  -> QntConstrPat . ConstrPat (Qual m c) <$> traverse renamePat ps

renameLAlt :: LQntAlt 'Parsed -> Rename (LQntAlt 'Renamed)
renameLAlt = traverse renameAlt

renameScheme :: Scheme Text -> Rename (Scheme Qual)
renameScheme (Scheme vs t) = Scheme vs <$> renameType t

renameLScheme :: LScheme Text -> Rename (LScheme Qual)
renameLScheme = traverse renameScheme

renameType :: Type Text -> Rename (Type Qual)
renameType = \case
  TName n -> findQualifiedType n >>= \case
               Nothing -> throwErr $ UnknownTypeErr n
               Just m  -> pure $ TName (Qual m n)
  TVar v     -> pure $ TVar v
  TApp t0 t1 -> TApp <$> renameType t0 <*> renameType t1

renameBind :: QntBind 'Parsed -> Rename (QntBind 'Renamed)
renameBind = \ case
  QntImpl n e   -> QntImpl n <$> renameLExpr e
  QntExpl n e s -> QntExpl n <$> renameLExpr e <*> renameLScheme s

renameData :: DataDecl 'Parsed -> Rename (DataDecl 'Renamed)
renameData (DataDecl x ps cs) = DataDecl x ps <$> traverse renameConstr cs

renameConstr :: DataConstr 'Parsed -> Rename (DataConstr 'Renamed)
renameConstr (DataConstr x as) = DataConstr x <$> traverse renameType as
