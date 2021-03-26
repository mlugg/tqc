{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}

module QntToNcl where

import Control.Monad
import Data.Functor
import Data.Foldable
import Common
import Tqc
import QntSyn
import NclSyn
import qualified Data.Text as T
import qualified Data.Set as S
import Data.Set (Set)
import Data.Traversable
import Data.List
import Data.Function

-- Convert monad {{{

newtype Convert a = Convert { runConvert :: Integer -> Tqc (a, Integer) }
  deriving (Functor)

runConvert' :: Convert a -> Tqc a
runConvert' m = fst <$> runConvert m 0

instance Applicative Convert where
  pure x = Convert $ \ n -> pure (x, n)
  (<*>) = ap

instance Monad Convert where
  m >>= f = Convert $ \ n0 -> do
    (x, n1) <- runConvert m n0
    runConvert (f x) n1

instance TqcMonad Convert where
  lift m = Convert $ \ n -> (, n) <$> m

freshName :: Convert LName
freshName = Convert $ \ n ->
  let name = T.pack $ "_gen_" <> show n
  in pure (GenName name, n + 1)

-- }}}

frees :: QntExpr 'Typechecked -> Set LName
frees = \ case
  QntVar (LoclName n) -> S.singleton n
  QntVar _ -> mempty
  QntNatLit _ -> mempty
  QntApp e0 e1 -> freesL e0 <> freesL e1
  QntLam (TcBinder n _) e -> S.delete (SrcName n) $ freesL e
  QntLet bs e ->
    let fs = foldMap freesL (e : fmap bindExpr bs)
    in fs S.\\ S.fromList (SrcName . bindName <$> bs)
  QntCase e as -> freesL e <> foldMap altFrees as

freesL :: LQntExpr 'Typechecked -> Set LName
freesL (L _ e) = frees e

freesL' :: LQntExpr 'Typechecked -> [NclBinder]
freesL' e = NclBinder <$> toList (freesL e)

altFrees :: LQntAlt 'Typechecked -> Set LName
altFrees (L _ (QntAlt p e)) = freesL e S.\\ patBinds p
  where patBinds = \ case
          QntNamePat (NamePat (TcBinder n _)) -> S.singleton (SrcName n)
          QntNatLitPat _ -> mempty
          QntConstrPat (ConstrPat _ ps) -> foldMap patBinds ps

convertBinder :: TcBinder -> NclBinder
convertBinder (TcBinder x _) = NclBinder (SrcName x)

convertBind :: QntBind 'Typechecked -> Convert NclBind
convertBind = \ case
  QntImpl b e   -> NclBind (convertBinder b) (freesL' e) <$> convertLExpr e
  QntExpl b e _ -> NclBind (convertBinder b) (freesL' e) <$> convertLExpr e

convertLExpr :: LQntExpr 'Typechecked -> Convert NclExpr
convertLExpr (L _ e) = convertExpr e

convertExpr :: QntExpr 'Typechecked -> Convert NclExpr
convertExpr = \ case
  QntVar v -> pure $ NclVar v
  QntNatLit x -> pure $ NclNatLit x
  QntApp e0 e1 -> NclApp <$> convertLExpr e0 <*> convertLExpr e1
  QntLam b e -> do
    let b' = convertBinder b
        fs = freesL' e \\ [b']
    e' <- convertLExpr e
    pure $ NclLam b' fs e'
  QntLet bs e -> NclLet
    <$> traverse convertBind bs
    <*> convertLExpr e
  QntCase e as -> do
    scrutLname <- freshName
    let scrutRname = LoclName scrutLname
    scrutBind <- NclBind (NclBinder scrutLname) (freesL' e) <$> convertLExpr e
    cvtdCase <- match [scrutRname] (as <&> \ (L _ (QntAlt p (L _ e'))) -> MatchAlt [p] e') caseDefaultErr
    -- We have to wrap the case in a let so that it's compiled lazily
    caseLname <- freshName
    let caseRname = LoclName caseLname
    let caseBind = NclBind (NclBinder caseLname) (NclBinder scrutLname : toList (NclBinder `S.map` foldMap altFrees as)) cvtdCase

    pure $ NclLet [scrutBind, caseBind] (NclVar caseRname)
  where caseDefaultErr = NclVar $ QualName $ Qual (Module []) "error"

data PatGroup
  = NamePatGroup [(NamePat 'Typechecked, MatchAlt)]
  | NatLitPatGroup [(NatLitPat, MatchAlt)]
  | ConstrPatGroup [(ConstrPat 'Typechecked, MatchAlt)]
  | NoPatGroup (QntExpr 'Typechecked)

data MatchAlt = MatchAlt [QntPat 'Typechecked] (QntExpr 'Typechecked)

mkPatGroups :: [MatchAlt] -> [PatGroup]
mkPatGroups = foldr f []
  where f (MatchAlt [] e) gs = NoPatGroup e : gs
        f (MatchAlt (QntNamePat n : as) e) (NamePatGroup ps : gs)
          = NamePatGroup ((n, MatchAlt as e) : ps) : gs
        f (MatchAlt (QntNatLitPat x : as) e) (NatLitPatGroup ps : gs)
          = NatLitPatGroup ((x, MatchAlt as e) : ps) : gs
        f (MatchAlt (QntConstrPat c : as) e) (ConstrPatGroup ps : gs)
          = ConstrPatGroup ((c, MatchAlt as e) : ps) : gs
        f (MatchAlt (QntNamePat n : as) e) gs
          = NamePatGroup [(n, MatchAlt as e)] : gs
        f (MatchAlt (QntNatLitPat x : as) e) gs
          = NatLitPatGroup [(x, MatchAlt as e)] : gs
        f (MatchAlt (QntConstrPat c : as) e) gs
          = ConstrPatGroup [(c, MatchAlt as e)] : gs

match :: [RName] -> [MatchAlt] -> NclExpr -> Convert NclExpr
match ns as def = foldrM (matchGroup ns) def (mkPatGroups as)

-- A helper function which groups natural literal patterns into groups
-- matching on the same value.
groupNatLitAlts :: [(NatLitPat, MatchAlt)] -> [(NatLitPat, [MatchAlt])]
groupNatLitAlts as =
  let as' = groupBy ((==) `on` fst) $ sortOn fst as
  in as' <&> \ xs -> (fst (head xs), snd <$> xs)

-- A helper data type, representing a group of sequential constructor
-- patterns looking for the same constructor. Contains the constructor,
-- and a list of the alternatives, each of which is made up of a list of
-- the subpatterns and a MatchAlt representing the remaining matches on
-- the alternative.
data SameConstrPatGroup = SameConstrPatGroup (Constr 'Typechecked) [([QntPat 'Typechecked], MatchAlt)]

groupConstrAlts :: [(ConstrPat 'Typechecked, MatchAlt)] -> [SameConstrPatGroup]
groupConstrAlts ps =
  let ps' = groupBy ((==) `on` constr) $ sortOn constr ps
  in ps' <&> \ xs -> SameConstrPatGroup (constr $ head xs) (xs <&> \ (ConstrPat _ subPats, a) -> (subPats, a))
  where constr (ConstrPat c _, _) = c

matchGroup :: [RName] -> PatGroup -> NclExpr -> Convert NclExpr
matchGroup [] (NoPatGroup e) _ = convertExpr e
matchGroup [] _ def = pure def
matchGroup (n:ns) g def = case g of
  NamePatGroup as ->
    let as' = as <&> \ (NamePat b, MatchAlt ps e) ->
          MatchAlt ps (QntLet [QntImpl b (L undefined $ QntVar n)] (L undefined e))
    in match ns as' def

  NatLitPatGroup as -> do
    as' <- for (groupNatLitAlts as) $ \ (NatLitPat x, subAlts) ->
      NclAlt (NclNatLitPat x) <$> match ns subAlts def
    pure $ NclCase n as' def

  ConstrPatGroup as -> do
    as' <- for (groupConstrAlts as) $ \ (SameConstrPatGroup constr alts) -> do
      -- Get the number of arguments to the constructor by looking at
      -- the number of sub-patterns in the group's first alternative
      let nargs = length $ fst $ head alts

      -- For each argument to the constructor, generate a fresh name and
      -- associated binder
      argsl <- replicateM nargs freshName
      let argsb = NclBinder <$> argsl :: [NclBinder]
          argsr = LoclName <$> argsl :: [RName]

      -- For each MatchAlt in the group, create a new one which also
      -- includes the subpatterns from this constructor
      let alts' = alts <&> \ (subpats, MatchAlt remainingPats e) ->
            MatchAlt (subpats <> remainingPats) e

      -- Create the final alternative; we look for the given
      -- constructor, saving its parameters into our generated names,
      -- and recursively match each alternative
      NclAlt (NclConstrPat constr argsb) <$> match (argsr <> ns) alts' def
    pure $ NclCase n as' def

  NoPatGroup e -> convertExpr e
