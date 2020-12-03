{-# LANGUAGE LambdaCase, OverloadedStrings, DataKinds, FlexibleInstances, DeriveFunctor, Safe #-}

module QntSyn.Tc where

import Data.Map (Map)
import qualified Data.Map as M
import Data.Text (Text)
import Data.Foldable
import Tqc
import QntSyn
import Data.Functor
import Data.Maybe
import Data.Traversable
import Control.Applicative
import Control.Monad

newtype TypeEnv = TypeEnv (Map RName Type)

fresh :: Infer TyVar
fresh = Infer $ \ e s u -> pure (TvUnif u, s, (u+1))

lookupConstr :: Qual -> Infer (Type, DataConstr)
lookupConstr = _

containsVar :: Type -> TyVar -> Bool
TVar v     `containsVar` u = v == u
TApp t0 t1 `containsVar` u = t0 `containsVar` u || t1 `containsVar` u
_          `containsVar` _ = False

singletonTypeEnv :: Text -> Type -> TypeEnv
singletonTypeEnv n t = TypeEnv $ M.singleton (LoclName $ SrcName n) t

instance Semigroup TypeEnv where
  TypeEnv m0 <> TypeEnv m1 = TypeEnv $ m0 <> m1

instance Monoid TypeEnv where
  mempty = TypeEnv mempty

lookupType :: RName -> Infer (Maybe Type)
lookupType n = Infer $ \ (TypeEnv e) s u ->
  let x = M.lookup n e in pure (x,s,u)

withEnv :: TypeEnv -> Infer a -> Infer a
withEnv (TypeEnv new) m = Infer $ \ (TypeEnv e) s u ->
  let e' = new <> e
  in runInfer m (TypeEnv e') s u

withType :: RName -> Type -> Infer a -> Infer a
withType n t m = Infer $ \ (TypeEnv e) s u ->
  let e' = M.insert n t e
  in runInfer m (TypeEnv e') s u

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
      Just t  -> pure (t, QntVar n)

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
    (te, e') <- withType (LoclName $ SrcName b) ta $ infer' e

    pure (ta `tArrow` te, QntLam (TcBinder b ta) e')

  QntLet bs e -> do
    _

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
    pure (singletonTypeEnv n tn, tn, QntNamePat (TcBinder n tn))

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
