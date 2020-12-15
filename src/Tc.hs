{-# LANGUAGE LambdaCase, OverloadedStrings, DataKinds, FlexibleInstances, DeriveFunctor, Safe #-}

module Tc where

import Data.Bifunctor
import Data.Either
import Data.Map (Map)
import qualified Data.Map as M
import Data.Map.Merge.Lazy
import Data.Set (Set)
import qualified Data.Set as S
import Data.Text (Text)
import qualified Data.Text as T
import qualified Data.Graph as G
import Data.Foldable
import Tqc
import Common
import QntSyn
import Data.Functor
import Data.Maybe
import Data.Traversable
import Control.Applicative
import Control.Monad

wrapTypeError :: (TypeError -> TypeError) -> Infer a -> Infer a
wrapTypeError f m = Infer $ \ te ke ce s u ->
  runInfer m te ke ce s u `tqcCatchErr` \case
    TypeErr tErr -> throwErr $ TypeErr (f tErr)
    err          -> throwErr err

withErrorExpr :: QntExpr 'Renamed -> Infer a -> Infer a
withErrorExpr e = wrapTypeError $ TeInExpr e

withErrorScheme :: Scheme RName -> Infer a -> Infer a
withErrorScheme e = wrapTypeError $ TeInScheme e

throwTypeErr :: TypeError -> Infer a
throwTypeErr = throwErr . TypeErr

-- Check whether one scheme can be an instance of another; i.e. is the
-- second at least as general as the first
isInstanceOf :: (Eq a) => Scheme a -> Scheme a -> Bool
s0 `isInstanceOf` s1 = isJust $ s0 `asInstanceOf` s1

-- Find a tyvar substitution that makes one scheme an instance of
-- another
asInstanceOf :: (Eq a) => Scheme a -> Scheme a -> Maybe (Map TyVar (Type a))
Scheme vsL tL `asInstanceOf` Scheme vsR tR = case (tL,tR) of
  (t, TVar n) -> do
    if n `S.member` vsR'
    then Just $ M.singleton n t -- Quantified in the RHS scheme, so can be anything in the LHS scheme
    else if n `S.member` vsL'
         then Nothing -- Var is quantified over in the LHS scheme but not the RHS, so they refer to different things
         else if t == TVar n
              then Just mempty -- Not quantified in either scheme and equivalent so refer to same type
              else Nothing -- Not quantified in either but not equivalent so refer to different types
  

  (TApp t0 t1, TApp t0' t1') -> do
    soln0 <- Scheme vsL t0 `asInstanceOf` Scheme vsR t0'
    soln1 <- Scheme vsL t1 `asInstanceOf` Scheme vsR t1'
    combine soln0 soln1

  (_, TApp _ _) -> Nothing

  (t, TName n) ->
    if t == TName n
    then Just mempty
    else Nothing

  where vsL' = S.map TvName vsL
        vsR' = S.map TvName vsR
        combine = mergeA
          preserveMissing
          preserveMissing
          (zipWithAMatched $
            \ _ t0 t1 -> if t0 == t1
                         then Just t0
                         else Nothing)
    
natType :: Type Qual
natType = TName (Qual (Module ["Data", "Nat"]) "Nat")

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

type TypeEnv = Map RName (Scheme Qual)
type KindEnv = Map Qual Kind
type ConstrEnv = Map Qual (Type Qual, [Type Qual])

fresh :: Infer TyVar
fresh = Infer $ \ _ _ _ s u -> pure (TvUnif u, s, (u+1))

lookupConstr :: Qual -> Infer (Type Qual, [Type Qual])
lookupConstr c = lookupConstr' c >>= \case
  Just x  -> pure x
  Nothing -> throwTypeErr _

lookupConstr' :: Qual -> Infer (Maybe (Type Qual, [Type Qual]))
lookupConstr' c = Infer $ \ _ _ e s u -> pure (M.lookup c e, s, u)

containsVar :: Type Qual -> TyVar -> Bool
TVar v     `containsVar` u = v == u
TApp t0 t1 `containsVar` u = t0 `containsVar` u || t1 `containsVar` u
_          `containsVar` _ = False

singletonTypeEnv :: Text -> Scheme Qual -> TypeEnv
singletonTypeEnv n t = M.singleton (LoclName $ SrcName n) t

lookupType :: RName -> Infer (Maybe (Scheme Qual))
lookupType n = Infer $ \ e _ _ s u ->
  let x = M.lookup n e in pure (x,s,u)

lookupKind :: Qual -> Infer (Maybe Kind)
lookupKind n = Infer $ \ _ e _ s u ->
  let x = M.lookup n e in pure (x,s,u)

typeVars :: Type Qual -> Set TyVar
typeVars = \case
  TName _    -> S.empty
  TVar v     -> S.singleton v
  TApp t0 t1 -> typeVars t0 <> typeVars t1

freeTvs :: Scheme Qual -> Set TyVar
freeTvs (Scheme vs t) = typeVars t S.\\ (S.map TvName vs)

getEnvFreeTvs :: Infer (Set TyVar)
getEnvFreeTvs = Infer $ \ e _ _ s u ->
  let vs = foldMap freeTvs e
  in pure (vs,s,u)

withEnv :: TypeEnv -> Infer a -> Infer a
withEnv new m = Infer $ \ te ke ce s u ->
  let te' = new <> te
  in runInfer m te' ke ce s u

withType :: RName -> Scheme Qual -> Infer a -> Infer a
withType n t m = Infer $ \ te ke ce s u ->
  let te' = M.insert n t te
  in runInfer m te' ke ce s u

getKind :: Type Qual -> Infer Kind
getKind = \case
  TName n ->
    lookupKind n >>= \case
      Just k -> pure k
      Nothing -> throwTypeErr _

  TVar _ -> pure KStar

  TApp t0 t1 -> do
    k <- getKind t1
    getKind t0 >>= \case
      KArrow kl kr | kl == k -> pure kr
      _ -> throwTypeErr _

checkKind :: Type Qual -> Infer ()
checkKind t = getKind t >>= \case
  KStar -> pure ()
  _     -> throwTypeErr _

withKindCheck :: Infer (Type Qual, a) -> Infer (Type Qual, a)
withKindCheck m = do
  (t,x) <- m
  checkKind t
  pure (t,x)

-- Substitutions {{{

newtype Substitution = Substitution (Map TyVar (Type Qual))

instance Semigroup Substitution where
  s0@(Substitution m0) <> s1 = Substitution $ m1 <> m0
    where Substitution m1 = applySub s0 s1

instance Monoid Substitution where
  mempty = Substitution mempty

class Substitute a where
  applySub :: Substitution -> a -> a

instance Substitute Substitution where
  applySub s (Substitution m) = Substitution $ fmap (applySub s) m

instance Substitute (Type Qual) where
  applySub s@(Substitution m) = \case
    TName n    -> TName n
    TVar v     -> fromMaybe (TVar v) (M.lookup v m)
    TApp t0 t1 -> TApp (applySub s t0) (applySub s t1)

instance Substitute (Scheme Qual) where
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

newtype Infer a = Infer { runInfer :: TypeEnv -> KindEnv -> ConstrEnv -> Substitution -> Integer -> Tqc (a, Substitution, Integer) }
  deriving (Functor)

instance Applicative Infer where
  pure x = Infer $ \ _ _ _ s u -> pure (x, s, u)
  (<*>) = ap

instance Monad Infer where
  m >>= f = Infer $ \ te ke ce s0 u0 -> do
    (x,s1,u1) <- runInfer m te ke ce s0 u0
    runInfer (f x) te ke ce s1 u1

instance TqcMonad Infer where
  lift m = Infer $ \ _ _ _ s u ->
    m <&> \ x -> (x,s,u)

-- }}}

replaceTyvars :: Map TyVar (Type Qual) -> Type Qual -> Type Qual
replaceTyvars m = go where
  go = \case
    TName x    -> TName x
    TVar v     -> M.findWithDefault (TVar v) v m
    TApp t0 t1 -> TApp (go t0) (go t1)

partitionEithersSet :: (Ord a, Ord b) => Set (Either a b) -> (Set a, Set b)
partitionEithersSet = bimap S.fromList S.fromList . partitionEithers . S.toList

generalize :: Set TyVar -> Type Qual -> Scheme Qual
generalize excl ty =
      -- Get all the tyvars mentioned in the type
  let allVars = typeVars ty

      -- Limit them to the ones we need to quantify over
      quantVars = allVars S.\\ excl

      -- Find the ones where we need to rename the var (each one with a
      -- numeric tyvar)
      (namedVars, unifVars) = partitionEithersSet $ S.map (\case { TvName n -> Left n; TvUnif u -> Right u }) quantVars

      -- Get the list of generated tyvar names we can use
      genNames = filter (\x -> TvName x `S.notMember` allVars) allGenNames
      
      -- Create a mapping from tyvars to tyvar names they should be replaced
      -- with
      tvMapping = M.fromList $ zip (S.toList $ S.map TvUnif unifVars) genNames

      -- Map TVar . TvName over the above to make a map from tyvars to
      -- the actual types they should be replaced with
      tvMapping' = TVar . TvName <$> tvMapping

      -- We quantify over both quantVars and the names we're replacing
      -- tyvars with
      allQuantVars = namedVars <> S.fromList (M.elems tvMapping)

  in Scheme allQuantVars (replaceTyvars tvMapping' ty)

  where allGenNames = fmap T.singleton ['a'..'z']
                   ++ fmap (T.cons 'a' . T.pack . show) [0 :: Integer ..]

instantiate :: Scheme Qual -> Infer (Type Qual)
instantiate (Scheme vs ty) = do
  tvs <- replicateM (S.size vs) fresh
  let m = M.fromList $ zip (TvName <$> S.toList vs) (TVar <$> tvs)
  pure $ replaceTyvars m ty

getSub :: Infer Substitution
getSub = Infer $ \ _ _ _ s u -> pure (s, s, u)

unify :: Type Qual -> Type Qual -> Infer ()
unify t0 t1 = do
  s  <- getSub
  case mgu (applySub s t0) (applySub s t1) of
    Left e   -> throwTypeErr e
    Right s' -> extendSub s'

extendSub :: Substitution -> Infer ()
extendSub s' = Infer $ \ _ _ _ s u -> pure ((), s <> s', u)

mgu :: Type Qual -> Type Qual -> Either TypeError Substitution
mgu = curry $ \case
  (TName x, TName y) -> if x == y
                        then Right mempty
                        else Left _

  (TVar x, TVar y) -> if x == y
                      then Right mempty
                      else Right $ Substitution $ M.singleton x (TVar y)

  (TVar v, t) -> if t `containsVar` v
                 then Left _
                 else Right $ Substitution $ M.singleton v t

  (t, TVar v) -> mgu (TVar v) t

  (TApp t0 t1, TApp t2 t3) -> liftA2 (<>) (mgu t0 t2) (mgu t1 t3)

  _ -> Left _

infer' :: LQntExpr 'Renamed -> Infer (Type Qual, LQntExpr 'Typechecked)
infer' (L loc e) = infer e <&> \(t,e') -> (t, L loc e')

infer :: QntExpr 'Renamed -> Infer (Type Qual, QntExpr 'Typechecked)
infer expr = withErrorExpr expr $ withKindCheck $ case expr of
  QntVar n ->
    lookupType n >>= \case
      Nothing -> throwTypeErr _
      Just s  -> instantiate s <&> \t -> (t, QntVar n)

  QntNatLit x ->
    pure (natType, QntNatLit x)

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
    traverse_ (unify tScrut) patTypes

    ue <- fresh
    let te = TVar ue
    traverse_ (unify te) exprTypes

    pure (te, QntCase eScrut' as')


inferPat :: QntPat 'Renamed -> Infer (TypeEnv, Type Qual, QntPat 'Typechecked)
inferPat = \case
  QntNamePat n -> do
    un <- fresh
    let tn = TVar un
    pure (singletonTypeEnv n (Scheme S.empty tn), tn, QntNamePat (TcBinder n tn))

  QntNatLitPat x ->
    pure (mempty, natType, QntNatLitPat x)

  QntConstrPat c ps -> do
    (tConstr, as) <- lookupConstr c

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
        QntImpl b e   -> Left  (b, e)
        QntExpl b e s -> Right (b, e, s)

      implGroups = mkBindGroups implBinds
      
      explEnvGiven = M.fromList $ explBinds <&> \(n, _, L _ s) -> (LoclName $ SrcName n, s)

  (fullEnv, implGroups') <- mapAccumLM f explEnvGiven implGroups

  let implBinds' = uncurry QntImpl <$> fold implGroups'

  -- Everything's inferred, but we need to check the types of the
  -- explicit bindings make sense!

  explBinds' <- withEnv fullEnv $
    for explBinds $ \(n,e,s) -> do
      (env, g) <- inferBindGroup [(n,e)]
      let e' = snd $ head g

      let inferred = env M.! LoclName (SrcName n)
      sub <- getSub
      let (L loc s') = applySub sub s
          inferred' = applySub sub inferred
          Scheme _ ty' = s'
      if s' `isInstanceOf` inferred'
      then pure $ QntExpl (TcBinder n ty') e' (L loc s')
      else throwTypeErr _

  pure (fullEnv, explBinds' <> implBinds')

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
  QntLet bs e ->
    let bound = S.fromList $ SrcName . bindName <$> bs
        exprs = e : fmap bindExpr bs
    in foldMap freeVars' exprs S.\\ bound

mkBindGroups :: [(Binder 'Renamed, LQntExpr 'Renamed)] -> [[(Binder 'Renamed, LQntExpr 'Renamed)]]
mkBindGroups bs =
  let nodes = bs <&> \(b,e) -> ((b,e), SrcName b, S.toList $ freeVars' e)
  in G.flattenSCC <$> G.stronglyConnComp nodes

inferBindGroup :: [(Binder 'Renamed, LQntExpr 'Renamed)] -> Infer (TypeEnv, [(Binder 'Typechecked, LQntExpr 'Typechecked)])
inferBindGroup bs = do
  initFreeTvs <- getEnvFreeTvs

  let (names, exprs) = unzip bs
      rnames = LoclName . SrcName <$> names

  tvs <- sequenceA $ fresh <$ bs

  let env = M.fromList $ zip rnames (Scheme S.empty . TVar <$> tvs)

  exprs' <- withEnv env $
           for (zip exprs tvs) $ \(L loc e, tv) -> do
             (t, e') <- infer e
             unify t (TVar tv)
             pure $ L loc e'

  s <- getSub

  let types = applySub s . TVar <$> tvs
      schemes = generalize initFreeTvs <$> types
    
      finalEnv = M.fromList $ zip rnames schemes

      binders = zipWith TcBinder names types

  pure (finalEnv, zip binders exprs')
