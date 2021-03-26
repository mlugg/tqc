{-# LANGUAGE LambdaCase, OverloadedStrings, DataKinds, FlexibleInstances, DeriveFunctor, Safe, MultiWayIf #-}

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

-- 'wrapTypeError f m' returns an action which runs 'm', but if it
-- throws a 'TypeError', mutates that error with 'f' before continuing.
wrapTypeError :: (TypeError -> TypeError) -> Infer a -> Infer a
wrapTypeError f m = Infer $ \ te ke ce s u ->
  runInfer m te ke ce s u `tqcCatchErr` \case
    TypeErr tErr -> throwErr $ TypeErr (f tErr)
    err          -> throwErr err

-- 'withErrorExpr e m' wraps any 'TypeError' thrown by 'm', specifying
-- that it originated in expression 'e'.
withErrorExpr :: LQntExpr 'Renamed -> Infer a -> Infer a
withErrorExpr e = wrapTypeError $ TeInExpr e

-- 'withErrorScheme s m' wraps any 'TypeError' thrown by 'm', specifying
-- that it originated in type scheme 's'.
withErrorScheme :: LScheme Qual -> Infer a -> Infer a
withErrorScheme e = wrapTypeError $ TeInScheme e

-- Throw the given type error; a simple wrapper around throwErr
throwTypeErr :: TypeError -> Infer a
throwTypeErr = throwErr . TypeErr

-- Check whether one scheme can be an instance of another; i.e. is the
-- second at least as general as the first
isInstanceOf :: Scheme Qual -> Scheme Qual -> Bool
s0 `isInstanceOf` s1 = isJust $ s0 `asInstanceOf` s1

-- Find a substitution that makes one scheme an instance of another
asInstanceOf :: Scheme Qual -> Scheme Qual -> Maybe (Map Text (Type Qual))
Scheme qsL tL `asInstanceOf` Scheme qsR tR =
  case (tL, tR) of -- Compare the types themselves, ignoring quantified variables

    -- To make a type an instance of a quantified tyvar, just assign
    -- that type to that variable
    (t, TName (Qual (Module []) n)) | n `S.member` qsR -> Just $ M.singleton n t

    -- If the names are equivalent and not quantified in either scheme,
    -- they refer to the same type. If it were quantified on the LHS,
    -- this would be invalid ('forall a. a' does not refer to the same
    -- type as 'forall b. a')
    (t, TName n) | t == TName n && n `S.notMember` qsL' -> Just mempty

    -- Any other unification with a name on the RHS is invalid
    (_, TName _) -> Nothing

    -- TVars act like unquantified TNames here; the only valid case, if
    -- the LHS type is a TVar, is for the types to be equivalent.
    (t, TVar x) | t == TVar x -> Just mempty

    -- ...hence, this case is invalid.
    (_, TVar _) -> Nothing

    (TApp t0 t1, TApp t0' t1') -> do
      -- Recursively apply the function to the constructors and
      -- arguments of the application, constructing schemes using the
      -- same sets of quantified variables 'vsL' and 'vsR'
      soln0 <- Scheme qsL t0 `asInstanceOf` Scheme qsR t0'
      soln1 <- Scheme qsL t1 `asInstanceOf` Scheme qsR t1'

      -- Combine the two sets of solutions (see helper function defined
      -- below)
      combine soln0 soln1

    -- Making any other type an instance of an application is impossible
    -- (this function is not commutative! We can make 'TApp _ _' an
    -- instance of 'forall a. a', but not the other way around).
    (_, TApp _ _) -> Nothing

  where -- qsL' is a slightly modified forms of qsL where each variable
        -- is wrapped in a 'Qual' constructor, making it a 'Qual' rather
        -- than a 'Text'. Used for some comparisons in the first case.
        qsL' = S.map (Qual (Module [])) qsL

        -- 'combine' takes two substitutions and merges them. The
        -- 'Data.Map.Merge.Lazy' module allows us to easily define a
        -- strategy for merging the two maps.
        combine = mergeA
          preserveMissing -- What to do with keys in the first map but not the second - preserve unchanged
          preserveMissing -- What to do with keys in the second map but not the first - preserve unchanged
          (zipWithAMatched $ -- What do do we keys in both maps - apply
                             -- the following function to the elements
                             -- to create a resulting element, or return
                             -- 'Nothing' to make map creation fail
            \ _ t0 t1 -> if t0 == t1   -- If the types are the same in both maps...
                         then Just t0  -- Then just yield that same type
                         else Nothing) -- Otherwise, we fail

-- The type of natural numbers (the only primitive numeric type
-- currently)
natType :: Type Qual
natType = TName (Qual (Module ["Data", "Nat"]) "Nat")

-- Helper function - 'mapAccumLM f z xs' applies the monadic function
-- 'f' to an accumulating state parameter 'z' and to each element of
-- 'xs' in turn. e.g.:
-- mapAccumLM (\ x y -> Just (x+1, show y)) 0 [True, False, True]
--   = Just (3, ["True", "False", "True"])
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

-- The type environment maps from resolved names (i.e. either local or
-- global) to type schemes
type TypeEnv = Map RName (Scheme Qual)

-- The kind environment maps from fully-qualified names (of types) to
-- those types' kinds
type KindEnv = Map Qual Kind

-- The constructor environment maps from fully-qualified names (of
-- constructors, which must be global, unlike e.g. normal functions) to
-- information about each of those constructors: the tyvars it is
-- quantified over, the type it constructs (in terms of those tyvars),
-- and the argument types (again, in terms of those tyvars).
type ConstrEnv = Map Qual (Set Text, Type Qual, [Type Qual]) -- type vars, resulting type, arg types

-- 'fresh' returns a 
fresh :: Infer TyVar
fresh = Infer $ \ _ _ _ s u -> pure (TyVar u, s, (u+1))

lookupConstr :: Qual -> Infer (Set Text, Type Qual, [Type Qual])
lookupConstr c = lookupConstr' c >>= \case
  Just x  -> pure x
  Nothing -> throwTypeErr $ TeUnknownVar (QualName c)

lookupConstr' :: Qual -> Infer (Maybe (Set Text, Type Qual, [Type Qual]))
lookupConstr' c = Infer $ \ _ _ e s u -> pure (M.lookup c e, s, u)

lookupInstantiateConstr :: Qual -> Infer (Type Qual, [Type Qual])
lookupInstantiateConstr c = do
  (vs, t, args) <- lookupConstr c
  tvs <- replicateM (S.size vs) fresh
  let m = M.fromList $ zip (S.toList vs) (TVar <$> tvs)
  pure $ (replaceNamedTypes m t, replaceNamedTypes m <$> args)

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

typeVars' :: Scheme Qual -> Set TyVar
typeVars' (Scheme _ t) = typeVars t

getEnvFreeTvs :: Infer (Set TyVar)
getEnvFreeTvs = Infer $ \ e _ _ s u ->
  let vs = foldMap typeVars' e
  in pure (vs,s,u)

withEnv :: TypeEnv -> Infer a -> Infer a
withEnv new m = Infer $ \ te ke ce s u ->
  let te' = new <> te
  in runInfer m te' ke ce s u

withKindEnv :: KindEnv -> Infer a -> Infer a
withKindEnv new m = Infer $ \ te ke ce s u ->
  let ke' = new <> ke
  in runInfer m te ke' ce s u

withConstrEnv :: ConstrEnv -> Infer a -> Infer a
withConstrEnv new m = Infer $ \ te ke ce s u ->
  let ce' = new <> ce
  in runInfer m te ke ce' s u

withType :: RName -> Scheme Qual -> Infer a -> Infer a
withType n t m = Infer $ \ te ke ce s u ->
  let te' = M.insert n t te
  in runInfer m te' ke ce s u

getKind :: Type Qual -> Infer Kind
getKind = \case
  TName n ->
    lookupKind n >>= \case
      Just k -> pure k
      Nothing -> throwTypeErr $ TeUnknownType n

  TVar _ -> pure KStar

  TApp t0 t1 -> do
    k <- getKind t1
    getKind t0 >>= \case
      KArrow kl kr | kl == k -> pure kr
      k' -> throwTypeErr $ TeBadTypeApp t0 k' t1 k

checkKind :: Type Qual -> Infer ()
checkKind t = getKind t >>= \case
  KStar -> pure ()
  _     -> throwTypeErr TeKindNotStar

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
    QntNamePat (NamePat n) -> QntNamePat (NamePat $ applySub s n)
    QntNatLitPat (NatLitPat x) -> QntNatLitPat (NatLitPat x)
    QntConstrPat (ConstrPat c ps) -> QntConstrPat $ ConstrPat c (applySub s <$> ps)

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

runInfer' :: TypeEnv -> KindEnv -> ConstrEnv -> Infer a -> Tqc (a, Substitution)
runInfer' te ke ce m = runInfer m te ke ce mempty 0 <&> \ (x, sub, _) -> (x, sub)

-- }}}

replaceNamedTypes :: Map Text (Type Qual) -> Type Qual -> Type Qual
replaceNamedTypes m = go where
  go = \ case
    t@(TName (Qual (Module []) x)) -> M.findWithDefault t x m
    TName x    -> TName x
    TVar v     -> TVar v
    TApp t0 t1 -> TApp (go t0) (go t1)

replaceTyvars :: Map TyVar (Type Qual) -> Type Qual -> Type Qual
replaceTyvars m = go where
  go = \ case
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

      -- Create a mapping from tyvars to names they should be replaced
      -- with
      tvMapping = M.fromList $ zip (S.toList quantVars) genNames

      -- Map TName over the above to make a map from tyvars to
      -- the actual types they should be replaced with
      tvMapping' = TName . Qual (Module []) <$> tvMapping

  in Scheme (S.fromList $ M.elems tvMapping) (replaceTyvars tvMapping' ty)

  where genNames = fmap T.singleton ['a'..'z']
                ++ fmap (T.cons 'a' . T.pack . show) [0 :: Integer ..]

instantiate :: Scheme Qual -> Infer (Type Qual)
instantiate (Scheme vs ty) = do
  tvs <- replicateM (S.size vs) fresh
  let m = M.fromList $ zip (S.toList vs) (TVar <$> tvs)
  pure $ replaceNamedTypes m ty

getSub :: Infer Substitution
getSub = Infer $ \ _ _ _ s u -> pure (s, s, u)

-- 'unify t0 t1' takes two types and attempts to unify them using 'mgu',
-- extending the current substitution if sucessful or throwing an error
-- otherwise.
unify :: Type Qual -> Type Qual -> Infer ()
unify t0 t1 = do
  s <- getSub
  case mgu (applySub s t0) (applySub s t1) of
    Left e   -> throwTypeErr e
    Right s' -> extendSub s'

-- 'extendSub s' modifies the current substitution by extending it with
-- 's'.
extendSub :: Substitution -> Infer ()
extendSub s' = Infer $ \ _ _ _ s u -> pure ((), s' <> s, u)

-- mgu finds the most general unifier for two types. That is, given a
-- type t0 and t1, 'mgu t0 t1' returns either a type error or a
-- substitution which, when applied to t0, will yield t1.
mgu :: Type Qual -> Type Qual -> Either TypeError Substitution
mgu = curry $ \case
  -- Unifying two named, concrete types is trivially only possible if
  -- those types are the same (we can't unify Nat with Bool for
  -- instance).
  (TName x, TName y) -> if x == y
                        then Right mempty
                        else Left $ TeTypeMismatch (TName x) (TName y)

  -- Unifying two type variables is done by substituting one for the
  -- other, unless they are the same, in which case no substitution is
  -- necessary.
  (TVar x, TVar y) -> if x == y
                      then Right mempty
                      else Right $ Substitution $ M.singleton x (TVar y)

  -- Unifying a tyvar with any other type is also done by a simple
  -- subtitution. However, we also need to check whether the type on the
  -- right contains the tyvar itself; if it does, we have an infinite
  -- type (e.g. 'a ~ List a') so return an error.
  (TVar v, t) -> if t `containsVar` v
                 then Left $ TeInfiniteType (TVar v) t
                 else Right $ Substitution $ M.singleton v t

  -- This is the same as the case above, but the other way around.
  (t, TVar v) -> mgu (TVar v) t

  -- To unify two type applications, we just unify the constructors and
  -- the arguments together (e.g. `Maybe a ~ Maybe b' is equivalent to
  -- 'Maybe ~ Maybe' and 'a ~ b').
  (TApp t0 t1, TApp t2 t3) -> liftA2 (<>) (mgu t0 t2) (mgu t1 t3)

  -- Attempts to unify any other types should fail.
  (t0, t1) -> Left $ TeTypeMismatch t0 t1

-- infer' is a variant of infer which acts on Located expressions, and
-- also wraps returned errors.
infer' :: LQntExpr 'Renamed -> Infer (Type Qual, LQntExpr 'Typechecked)
infer' el@(L loc e) = withErrorExpr el (infer e) <&> \(t,e') -> (t, L loc e')

-- infer is the main inference function, which takes a Renamed
-- expression and returns its type and an equivalent Typechecked
-- expression.
infer :: QntExpr 'Renamed -> Infer (Type Qual, QntExpr 'Typechecked)
infer = withKindCheck . \case -- withKindCheck here enforces that every term must have a type of kind *; e.g. no term may have type 'Maybe'

  -- A variable reference is simply resolved by looking up that name in
  -- the type environment.
  QntVar n ->
    lookupType n >>= \case
      Nothing -> throwTypeErr $ TeUnknownVar n
      Just s  -> instantiate s <&> \t -> (t, QntVar n)

  -- The type of a literal is hardcoded (see the natType constant
  -- earlier in this module).
  QntNatLit x ->
    pure (natType, QntNatLit x)

  QntApp ef ea -> do
    -- Create a new type variable to represent the function's result
    -- type
    ur <- fresh
    let tr = TVar ur

    -- Infer the type of the function and its argument, also receiving
    -- modified (Typechecked rather than Renamed) expressions
    (tf, ef') <- infer' ef
    (ta, ea') <- infer' ea

    -- Through unification, enforce that 'tf ~ ta -> tr'
    unify tf (ta `tArrow` tr)

    -- Return the created result type and Typechecked expression
    pure (tr, QntApp ef' ea')

  QntLam b e -> do
    -- Create a type variable to represent the lambda's argument type
    ua <- fresh
    let ta = TVar ua

    -- Extend the type environment with the fact that 'x : ta' for the
    -- lambda argument 'x', and within this environment, infer the type
    -- of the body expression
    (te, e') <- withType (LoclName $ SrcName b) (Scheme S.empty ta) $ infer' e

    -- The lambda's type is a function from the argument type 'ta' to
    -- the body result type 'te'
    pure (ta `tArrow` te, QntLam (TcBinder b ta) e')

  QntLet bs e -> do
    -- Take the set of bindings and infer the type schemes of them all
    -- using inferBinds
    (env, bs') <- inferBinds bs

    -- Extend the type environment with all the bound names, and infer
    -- the type of the 'in ...' expression within this new environment
    (te, e') <- withEnv env $ infer' e

    -- Return the type of this body expression and a Typechecked
    -- expression
    pure (te, QntLet bs' e')

  QntCase eScrut as -> do
    (patTypes, exprTypes, as') <-
      -- unzip3 helps convert our list of tuples to a tuple of lists
      fmap unzip3 $
      -- For each alternative with source location 'loc', pattern 'p',
      -- and RHS expression 'e'...
      for as $ \(L loc (QntAlt p e)) -> do
        -- Infer the type of the pattern. Here, 'env' is the type
        -- environment introduced by the pattern's bound variables, 'tp'
        -- is the type of the scrutinee, and 'p'' is the Typechecked
        -- pattern.
        (env, tp, p') <- inferPat p

        -- Within an environment extended by the pattern's bound
        -- variables, infer the type of the alternative's RHS.
        (te, e') <- withEnv env $ infer' e

        -- Return the scrutinee type, the RHS type, and the Typechecked
        -- alternative.
        pure (tp, te, L loc $ QntAlt p' e')

    -- Now:
    -- - patTypes is a list of every type the scrutinee must match
    -- - exprTypes is a list of the types of every alternative's RHS
    -- - as' is the list of Typechecked alternatives

    -- Infer the actual type 'tScrut' of the scrutinee
    (tScrut, eScrut') <- infer' eScrut

    -- Unify each type in 'patTypes' with 'tScrut', ensuring the
    -- scrutinee type is as expected by each pattern
    traverse_ (unify tScrut) patTypes

    -- Create a type variable to represent the resulting type of the
    -- expression.
    ue <- fresh
    let te = TVar ue

    -- As this case expression itself must have a concrete type, unify
    -- each type in 'exprTypes' with the tyvar created above.
    traverse_ (unify te) exprTypes

    -- Return the created type and the Typechecked case statement.
    pure (te, QntCase eScrut' as')

-- inferPat infers types around patterns; given a Renamed pattern, it
-- returns the type environment introduced by binders in the pattern,
-- the type which the expression being scruntinised must have, and an
-- equivalent Typechecked pattern.
inferPat :: QntPat 'Renamed -> Infer (TypeEnv, Type Qual, QntPat 'Typechecked)
inferPat = \case
  -- Name patterns introduce a binding into the environment of the bound
  -- name to a new type. We represent this by creating a fresh type
  -- variable which represents the bound variable's type, returning it
  -- in the environment, and also requiring the scruntinised expression
  -- to have that same type.
  QntNamePat (NamePat n) -> do
    un <- fresh
    let tn = TVar un
    pure (singletonTypeEnv n (Scheme S.empty tn), tn, QntNamePat (NamePat $ TcBinder n tn))

  -- Numeric literal patterns don't introduce any bound variables, but
  -- they do enforce that the scrutinee is of type 'Nat'.
  QntNatLitPat (NatLitPat x) ->
    pure (mempty, natType, QntNatLitPat (NatLitPat x))

  QntConstrPat (ConstrPat c ps) -> do
    -- Lookup the given constructor, and instantiate it with new type
    -- variables to prevent it conflicting with different uses of the
    -- same constructor. This returns 'tConstr', the type which the
    -- constructor results in (here, the scrutinee type), and 'as', the
    -- types of each argument to the constructor.
    (tConstr, as) <- lookupInstantiateConstr c

    -- Sub-patterns and constructor arguments should be in a one-to-one
    -- correspondence
    when (length as /= length ps) $ throwTypeErr $ TeBadPatternArgs c (length as) (length ps)

    (es,ps') <-
      fmap unzip $
      -- For every pattern 'p' matching a constructor argument of type
      -- 'a'...
      for (zip ps as) $ \(p,a) -> do
        -- Recursively infer the type of the sub-pattern 'p', returning
        -- the expected type of the argument in 't', the introduced
        -- environment in 'e', and the Typechecked pattern in 'p''
        (e,t,p') <- inferPat p

        -- unify the expected argument type with its actual type
        unify t a

        -- Return the environment introduced by the sub-pattern, as well
        -- as the sub-pattern's Typechecked variant.
        pure (e,p')

    -- Now, 'es' is a list of every environment introduced by the
    -- sub-patterns, as 'ps'' is a list of the Typechecked variants of
    -- the patterns in 'ps'

    -- Combine all the environments into one with 'fold', give the
    -- scruntinee the known constructor type, and return the Typechecked
    -- pattern
    pure (fold es, tConstr, QntConstrPat $ ConstrPat c ps')

inferBinds :: [QntBind 'Renamed] -> Infer (TypeEnv, [QntBind 'Typechecked])
inferBinds bs = do
  let (implBinds, explBinds) = partitionEithers $ bs <&> \case
        QntImpl b e   -> Left  (b, e)
        QntExpl b e s -> Right (b, e, s)

      implGroups = mkBindGroups (LoclName . SrcName) implBinds
      
      explEnvGiven = M.fromList $ explBinds <&> \(n, _, L _ s) -> (LoclName $ SrcName n, s)

  (fullEnv, implGroups') <- mapAccumLM f explEnvGiven implGroups

  let implBinds' = uncurry QntImpl <$> fold implGroups'

  -- Everything's inferred, but we need to check the types of the
  -- explicit bindings make sense!

  explBinds' <- withEnv fullEnv $
    for explBinds $ \(n,e,s) -> do
      (env, g) <- inferBindGroup (LoclName . SrcName) [(n,e)]
      let e' = snd $ head g

      let inferred = env M.! LoclName (SrcName n)
      sub <- getSub
      let (L loc s') = applySub sub s
          inferred' = applySub sub inferred
          Scheme _ ty' = s'
      if s' `isInstanceOf` inferred'
      then pure $ QntExpl (TcBinder n ty') e' (L loc s')
      else throwTypeErr $ TeSchemeMismatch s' inferred'

  pure (fullEnv, explBinds' <> implBinds')

  where f curEnv g = do
          (newEnv, g') <- withEnv curEnv $ inferBindGroup (LoclName . SrcName) g
          pure (newEnv <> curEnv, g')

patBinds :: QntPat 'Renamed -> Set RName
patBinds = \case
  QntNamePat (NamePat n) -> S.singleton (LoclName $ SrcName n)
  QntNatLitPat _ -> S.empty
  QntConstrPat (ConstrPat _ ps) -> foldMap patBinds ps

freeVars' :: LQntExpr 'Renamed -> Set RName
freeVars' (L _ e) = freeVars e

freeVars :: QntExpr 'Renamed -> Set RName
freeVars = \case
  QntVar n -> S.singleton n
  QntNatLit _ -> S.empty
  QntApp e0 e1 -> freeVars' e0 <> freeVars' e1
  QntLam b e -> S.delete (LoclName $ SrcName b) $ freeVars' e
  QntCase scrut as -> freeVars' scrut <> foldMap (\(L _ (QntAlt p e)) -> freeVars' e S.\\ patBinds p) as
  QntLet bs e ->
    let bound = S.fromList $ LoclName . SrcName . bindName <$> bs
        exprs = e : fmap bindExpr bs
    in foldMap freeVars' exprs S.\\ bound

mkBindGroups :: (Text -> RName) -> [(Binder 'Renamed, LQntExpr 'Renamed)] -> [[(Binder 'Renamed, LQntExpr 'Renamed)]]
mkBindGroups mkName bs =
  let nodes = bs <&> \(b,e) -> ((b,e), mkName b, S.toList $ freeVars' e)
  in G.flattenSCC <$> G.stronglyConnComp nodes

inferBindGroup :: (Text -> RName) -> [(Binder 'Renamed, LQntExpr 'Renamed)] -> Infer (TypeEnv, [(Binder 'Typechecked, LQntExpr 'Typechecked)])
inferBindGroup mkName bs = do
  initFreeTvs <- getEnvFreeTvs

  let (names, exprs) = unzip bs
      rnames = mkName <$> names

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

checkDataConstrs :: Module -> DataDecl 'Renamed -> Infer (DataDecl 'Typechecked)
checkDataConstrs modu (DataDecl typeName ps cs) = do
  let argKe = M.fromList $ ps <&> \ (TyParam x k) -> (Qual modu x, k)
  cs' <- withKindEnv argKe $ traverse checkConstr cs
  pure $ DataDecl typeName ps cs'

checkConstr :: DataConstr 'Renamed -> Infer (DataConstr 'Typechecked)
checkConstr (DataConstr x as) = do
  traverse_ checkKind as
  pure $ DataConstr x as

inferTopLevelBinds :: Module -> [QntBind 'Renamed] -> Infer (TypeEnv, [QntBind 'Typechecked])
inferTopLevelBinds modu bs = do
  let (implBinds, explBinds) = partitionEithers $ bs <&> \case
        QntImpl b e   -> Left  (b, e)
        QntExpl b e s -> Right (b, e, s)

      implGroups = mkBindGroups (QualName . Qual modu) implBinds
      
      explEnvGiven = M.fromList $ explBinds <&> \(n, _, L _ s) -> (QualName $ Qual modu n, s)

  (fullEnv, implGroups') <- mapAccumLM f explEnvGiven implGroups

  let implBinds' = uncurry QntImpl <$> fold implGroups'

  -- Everything's inferred, but we need to check the types of the
  -- explicit bindings make sense!

  explBinds' <- withEnv fullEnv $
    for explBinds $ \(n,e,s) -> do
      (env, g) <- inferBindGroup (QualName . Qual modu) [(n,e)]
      let e' = snd $ head g

      let inferred = env M.! QualName (Qual modu n)
      sub <- getSub
      let (L loc s') = applySub sub s
          inferred' = applySub sub inferred
          Scheme _ ty' = s'
      if s' `isInstanceOf` inferred'
      then pure $ QntExpl (TcBinder n ty') e' (L loc s')
      else throwTypeErr $ TeSchemeMismatch s' inferred'

  pure (fullEnv, explBinds' <> implBinds')

  where f curEnv g = do
          (newEnv, g') <- withEnv curEnv $ inferBindGroup (QualName . Qual modu) g
          pure (newEnv <> curEnv, g')
