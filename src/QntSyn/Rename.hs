{-# LANGUAGE Safe, LambdaCase, DataKinds, DeriveFunctor, OverloadedStrings #-}

module QntSyn.Rename where

import Tqc
import QntSyn
import Data.Text (Text)
import Data.Set (Set)
import qualified Data.Set as S
import Control.Monad
import Data.Traversable

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

renameExpr :: Expr 'Parsed -> Rename (Expr 'Renamed)
renameExpr = \case
  EName n -> do
    isLocal <- lookupLocal n
    if isLocal
    then pure $ EName (LoclName n)
    else findQualified n >>= \case
      Nothing -> throwErr _ -- TODO XXX
      Just m  -> pure $ EName (QualName m n)

  ELet bs body ->
    let names = S.fromList $ bindName <$> bs
    in withLocals names $ do
      bs' <- for bs $ \b ->
        case b of
          BindingImpl n e   -> BindingImpl n <$> renameLExpr e
          BindingExpl n e t -> BindingExpl n <$> renameLExpr e <*> pure t

      body' <- renameLExpr body

      pure $ ELet bs' body'


  ECase e as ->
    ECase
    <$> renameLExpr e
    <*> traverse renameLAlt as

  ENatLit x -> pure $ ENatLit x

  EAppl e0 e1 ->
    EAppl
    <$> renameLExpr e0
    <*> renameLExpr e1

  ELambda x e -> withLocal x $
    ELambda x <$> renameLExpr e

renameLExpr :: LExpr 'Parsed -> Rename (LExpr 'Renamed)
renameLExpr = traverse renameExpr

renameAlt :: Alt 'Parsed -> Rename (Alt 'Renamed)
renameAlt (Alt p e) =
  let ns = findPatNames p
  in withLocals ns $ Alt p <$> renameLExpr e
  where
    findPatNames = \case
      PName x -> S.singleton x
      PNatLit _ -> S.empty
      PConstr _ ps -> foldMap findPatNames ps

renameLAlt :: LAlt 'Parsed -> Rename (LAlt 'Renamed)
renameLAlt = traverse renameAlt

findQualified :: Text -> Rename (Maybe Module)
findQualified x = pure $ Just $ Module ["Foo", x] -- XXX TODO
