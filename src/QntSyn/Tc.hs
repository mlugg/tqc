{-# LANGUAGE LambdaCase, OverloadedStrings, DataKinds, FlexibleInstances, DeriveFunctor, Safe #-}

module QntSyn.Tc where

import Data.Either
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Graph as G
import Data.Foldable
import Tqc
import QntSyn
import Data.Functor
import Data.Maybe
import Data.Traversable
import Control.Applicative
import Control.Monad

mapAccumLM :: (Monad m)
           => (a -> b -> m (a, c))
           -> a
           -> [b]
           -> m (a, [c])

mapAccumLM f = go where
  go z [] = pure (z, [])
  go z (x:xs) = do
    (z0, y) <- f z x
    (z1, ys) <- go z0 xs
    pure (z1, y:ys)

type TypeEnv = Map RName Scheme

fresh :: Infer TyVar
fresh = Infer $ \ e s u -> pure (TvUnif u, s, (u+1))

lookupConstr :: Qual -> Infer (Type, DataConstr)
lookupConstr = _

containsVar :: Type -> TyVar -> Bool
TVar v     `containsVar` u = v == u
TApp t0 t1 `containsVar` u = t0 `containsVar` u || t1 `containsVar` u
_          `containsVar` _ = False

singletonTypeEnv :: Text -> Scheme -> TypeEnv
singletonTypeEnv n t = M.singleton (LoclName $ SrcName n) t

lookupType :: RName -> Infer (Maybe Scheme)
lookupType n = Infer $ \ e s u ->
  let x = M.lookup n e in pure (x,s,u)

typeVars :: Type -> Set TyVar
typeVars = \case
  TName _    -> S.empty
  TVar v     -> S.singleton v
  TApp t0 t1 -> typeVars t0 <> typeVars t1

freeTvs :: Scheme -> Set TyVar
freeTvs (Scheme vs t) = typeVars t S.\\ (S.map TvName vs)

getEnvFreeTvs :: Infer (Set TyVar)
getEnvFreeTvs = Infer $ \ e s u ->
  let vs = foldMap freeTvs e
  in pure (vs,s,u)

withEnv :: TypeEnv -> Infer a -> Infer a
withEnv new m = Infer $ \ e s u ->
  let e' = new <> e
  in runInfer m e' s u

withType :: RName -> Scheme -> Infer a -> Infer a
withType n t m = Infer $ \ e s u ->
  let e' = M.insert n t e
  in runInfer m e' s u

-- Substitutions {{{

newtype Substitution = Substitution (Map TyVar Type)

instance Semigroup Substitution where
  s0@(Substitution m0) <> s1 = Substitution $ m1 <> m0
    where Substitution m1 = applySub s0 s1

instance Monoid Substitution where
  mempty = Substitution mempty

class Substitute a where
  applySub :: Substitution -> a -> a

instance Substitute Substitution where
  applySub s (Substitution m) = Substitution $ fmap (applySub s) m

instance Substitute Type where
  applySub s@(Substitution m) = \case
    TName n    -> TName n
    TVar v     -> fromMaybe (TVar v) (M.lookup v m)
    TApp t0 t1 -> TApp (applySub s t0) (applySub s t1)

instance Substitute Scheme where
  applySub s (Scheme fs t) = Scheme fs (applySub s t)

instance Substitute TcBinder where
  applySub s (TcBinder n t) = TcBinder n (applySub s t)

instance Substitute (QntExpr 'Typechecked) where
  applySub s = \case
    QntVar n -> QntVar n
    QntNatLit x -> QntNatLit x
    QntApp e0 e1 -> QntApp (applySub s e0) (applySub s e1)
    QntLam b e -> QntLam (applySub s b) (applySub s e)
    QntLet bs e -> QntLet (applySub s <$> bs) (applySub s e)
    QntCase e as -> QntCase (applySub s e) (applySub s <$> as)

instance Substitute (QntBind 'Typechecked) where
  applySub s = \case
    QntImpl b e   -> QntImpl (applySub s b) (applySub s e)
    QntExpl b e t -> QntExpl (applySub s b) (applySub s e) t -- We don't apply the subtitution to the explicit type as this is user-supplied and should not be modified

instance Substitute (QntAlt 'Typechecked) where
  applySub s (QntAlt p e) = QntAlt (applySub s p) (applySub s e)

instance Substitute (QntPat 'Typechecked) where
  applySub s = \case
    QntNamePat n -> QntNamePat (applySub s n)
    QntNatLitPat x -> QntNatLitPat x
    QntConstrPat c ps -> QntConstrPat c (applySub s <$> ps)

instance (Substitute a) => Substitute (Located a) where
  applySub s (L p x) = L p (applySub s x)

-- }}}

-- Inference monad {{{

newtype Infer a = Infer { runInfer :: TypeEnv -> Substitution -> Integer -> Tqc (a, Substitution, Integer) }
  deriving (Functor)

instance Applicative Infer where
  pure x = Infer $ \ e s u -> pure (x, s, u)
  (<*>) = ap

instance Monad Infer where
  m >>= f = Infer $ \ e s0 u0 -> do
    (x,s1,u1) <- runInfer m e s0 u0
    runInfer (f x) e s1 u1

instance TqcMonad Infer where
  lift m = Infer $ \ e s u ->
    m <&> \ x -> (x,s,u)

-- }}}

replaceTyvars :: Map TyVar Type -> Type -> Type
replaceTyvars m = go where
  go = \case
    TName x    -> TName x
    TVar v     -> M.findWithDefault (TVar v) v m
    TApp t0 t1 -> TApp (go t0) (go t1)

generalize :: Set TyVar -> Type -> Scheme
generalize excl ty =
      -- Get all the tyvars mentioned in the type
  let allVars = typeVars ty

      -- Limit them to the ones we need to quantify over
      quantVars = allVars S.\\ excl

      -- Find the ones where we need to rename the var (each one with a
      -- numeric tyvar)
      renameVars = S.filter (\case { TvName _ -> False; TvUnif _ -> True }) quantVars

      -- Get the list of generated tyvar names we can use
      genNames = filter (\x -> TvName x `S.notMember` allVars) allGenNames
      
      -- Create a mapping from tyvars to tyvar names they should be replaced
      -- with
      tvMapping = M.fromList $ zip (S.toList renameVars) genNames

      -- Map TVar . TvName over the above to make a map from tyvars to
      -- the actual types they should be replaced with
      tvMapping' = TVar . TvName <$> tvMapping

      -- We quantify over both quantVars and the names we're replacing
      -- tyvars with
      allQuantVars = S.map (\(TvName x) -> x) quantVars <> S.fromList (M.elems tvMapping)

  in Scheme allQuantVars (replaceTyvars tvMapping' ty)

  where allGenNames = fmap T.singleton ['a'..'z']
                   ++ fmap (T.cons 'a' . T.pack . show) [0..]

instantiate :: Scheme -> Infer Type
instantiate (Scheme vs ty) = do
  tvs <- replicateM (S.size vs) fresh
  let m = M.fromList $ zip (TvName <$> S.toList vs) (TVar <$> tvs)
  pure $ replaceTyvars m ty

getSub :: Infer Substitution
getSub = Infer $ \ e s u -> pure (s, s, u)

unify :: Type -> Type -> Infer ()
unify t0 t1 = do
  s  <- getSub
  s' <- mgu (applySub s t0) (applySub s t1)
  extendSub s'

extendSub :: Substitution -> Infer ()
extendSub s' = Infer $ \ e s u -> pure ((), s <> s', u)

mgu :: Type -> Type -> Infer Substitution
mgu = curry $ \case
  (TName x, TName y) -> if x == y
                        then pure mempty
                        else throwErr _

  (TVar x, TVar y) -> if x == y
                      then pure mempty
                      else throwErr _

  (TVar v, t) -> if t `containsVar` v
                 then throwErr _
                 else pure $ Substitution $ M.singleton v t

  (t, TVar v) -> mgu (TVar v) t

  (TApp t0 t1, TApp t2 t3) -> liftA2 (<>) (mgu t0 t2) (mgu t1 t3)

  _ -> throwErr _

infer' :: LQntExpr 'Renamed -> Infer (Type, LQntExpr 'Typechecked)
infer' (L loc e) = infer e <&> \(t,e') -> (t, L loc e')

infer :: QntExpr 'Renamed -> Infer (Type, QntExpr 'Typechecked)
infer = \case
  QntVar n ->
    lookupType n >>= \case
      Nothing -> throwErr _
      Just s  -> instantiate s <&> \t -> (t, QntVar n)

  QntNatLit x ->
    pure (TName "Nat", QntNatLit x)

  QntApp ef ea -> do
    ur <- fresh
    let tr = TVar ur

    (tf, ef') <- infer' ef
    (ta, ea') <- infer' ea

    unify tf (ta `tArrow` tr)

    pure (tr, QntApp ef' ea')

  QntLam b e -> do
    ua <- fresh
    let ta = TVar ua
    (te, e') <- withType (LoclName $ SrcName b) (Scheme S.empty ta) $ infer' e

    pure (ta `tArrow` te, QntLam (TcBinder b ta) e')

  QntLet bs e -> do
    (env, bs') <- inferBinds bs
    (te, e') <- withEnv env $ infer' e
    pure (te, QntLet bs' e')

  QntCase eScrut as -> do
    (patTypes, exprTypes, as') <-
      fmap unzip3 $
      for as $ \(L loc (QntAlt p e)) -> do
        (env, tp, p') <- inferPat p
        (te, e') <- withEnv env $ infer' e
        pure (tp, te, L loc $ QntAlt p' e')

    (tScrut, eScrut') <- infer' eScrut
    traverse (unify tScrut) patTypes

    ue <- fresh
    let te = TVar ue
    traverse (unify te) exprTypes

    pure (te, QntCase eScrut' as')


inferPat :: QntPat 'Renamed -> Infer (TypeEnv, Type, QntPat 'Typechecked)
inferPat = \case
  QntNamePat n -> do
    un <- fresh
    let tn = TVar un
    pure (singletonTypeEnv n (Scheme S.empty tn), tn, QntNamePat (TcBinder n tn))

  QntNatLitPat x ->
    pure (mempty, TName "Nat", QntNatLitPat x)

  QntConstrPat c ps -> do
    (tConstr, DataConstr _ as) <- lookupConstr c

    (es,ps') <-
      fmap unzip $
      for (zip ps as) $ \(p,a) -> do
        (e,t,p') <- inferPat p
        unify t a
        pure (e,p')

    pure (fold es, tConstr, QntConstrPat c ps')

inferBinds :: [QntBind 'Renamed] -> Infer (TypeEnv, [QntBind 'Typechecked])
inferBinds bs = do
  let (implBinds, explBinds) = partitionEithers $ bs <&> \case
        QntImpl b e   -> Left   (b,e)
        QntExpl b e s -> Right ((b,e),s)

      implGroups = mkBindGroups implBinds
      
      explEnvGiven = M.fromList $ explBinds <&> \((n, _), L _ s) -> (LoclName $ SrcName n, s)

  (fullEnv, implGroups') <- mapAccumLM f explEnvGiven implGroups

  let implBinds' = mconcat implGroups'

  -- Everything's inferred, but we need to check the types of the
  -- explicit bindings make sense!
  -- TODO: that

  _

  where f curEnv g = do
          (newEnv, g') <- withEnv curEnv $ inferBindGroup g
          pure (newEnv <> curEnv, g')

patBinds :: QntPat 'Renamed -> Set LName
patBinds = \case
  QntNamePat n -> S.singleton (SrcName n)
  QntNatLitPat _ -> S.empty
  QntConstrPat _ ps -> foldMap patBinds ps

freeVars' :: LQntExpr 'Renamed -> Set LName
freeVars' (L _ e) = freeVars e

freeVars :: QntExpr 'Renamed -> Set LName
freeVars = \case
  QntVar (LoclName n) -> S.singleton n
  QntVar _ -> S.empty
  QntNatLit _ -> S.empty
  QntApp e0 e1 -> freeVars' e0 <> freeVars' e1
  QntLam b e -> S.delete (SrcName b) $ freeVars' e
  QntCase scrut as -> freeVars' scrut <> foldMap (\(L _ (QntAlt p e)) -> freeVars' e S.\\ patBinds p) as

mkBindGroups :: [(Binder 'Renamed, LQntExpr 'Renamed)] -> [[(Binder 'Renamed, LQntExpr 'Renamed)]]
mkBindGroups bs =
  let nodes = bs <&> \(b,e) -> ((b,e), SrcName b, S.toList $ freeVars' e)
  in G.flattenSCC <$> G.stronglyConnComp nodes

inferBindGroup :: [(Binder 'Renamed, LQntExpr 'Renamed)] -> Infer (TypeEnv, [(Binder 'Typechecked, LQntExpr 'Typechecked)])
inferBindGroup bs = do
  freeTvs <- getEnvFreeTvs

  let names  = fst <$> bs
      rnames = LoclName . SrcName <$> names

  tvs <- sequenceA $ fresh <$ bs

  let env = M.fromList $ zip rnames (Scheme S.empty . TVar <$> tvs)

  exprs <- withEnv env $
           for (zip bs tvs) $ \((name, L loc e), tv) -> do
             (t, e') <- infer e
             unify t (TVar tv)
             pure $ L loc e'

  s <- getSub

  let types = applySub s . TVar <$> tvs
      schemes = generalize freeTvs <$> types
    
      finalEnv = M.fromList $ zip rnames schemes

      binders = zipWith TcBinder names types

  pure (finalEnv, zip binders exprs)
