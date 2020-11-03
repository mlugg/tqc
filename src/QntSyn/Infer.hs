{-# LANGUAGE LambdaCase, GeneralizedNewtypeDeriving, OverloadedStrings #-}

module QntSyn.Infer where

import Debug.Trace

import qualified Data.Text as T
import QntSyn
import Data.Text (Text)
import Data.Map (Map)
import qualified Data.Map as M
import Data.Set (Set)
import qualified Data.Set as S
import qualified Data.Graph as G
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.Except
import Data.Functor
import Data.Maybe
import Data.Either

newtype Subs = Subs { unSubs :: Map Integer Type }
  deriving (Show)

instance Semigroup Subs where
  s0 <> s1 = Subs $ M.map (applySubs s1) (unSubs s0) <> (unSubs s1)

instance Monoid Subs where
  mempty = Subs $ M.empty
  

data TypeError = TE_ Text
  deriving (Show)

type TypeEnv = Map Text TypeScheme

data InferEnv = InferEnv
   { envTypeEnv :: TypeEnv
   , envConstrs :: Map Text DataConstr
   } deriving (Show)

doInfer :: Expr -> Either TypeError TypeScheme
doInfer e = fmap (\(t,(_,s)) -> generalize 0 $ applySubs s t) $ runExcept $ runStateT (runReaderT (unInfer $ infer e) (InferEnv M.empty M.empty)) (0, mempty)

newtype Infer a = Infer
  { unInfer :: 
      ReaderT InferEnv
        (StateT (Integer, Subs)
          (Except TypeError)
        )
      a
  } deriving
    ( Functor
    , Applicative
    , Monad
    , MonadReader InferEnv
    , MonadState (Integer, Subs)
    , MonadError TypeError
    )

-- Utility functions {{{

-- TODO FIXME XXX
-- |x `fitsScheme` y checks whether type scheme x is equivalent to or
-- a specialization of type scheme y.
fitsScheme :: TypeScheme -> TypeScheme -> Bool
fitsScheme x y = trace ("fitsscheme (" <> show x <> ") (" <> show y <> ")") $ x == y

findRefs :: Expr -> Set Text
findRefs = \case
  EName x -> S.singleton x
  ENatLit _ -> S.empty
  EAppl ef ex -> findRefs ef <> findRefs ex
  ELambda x e -> S.delete x $ findRefs e
  ECase e ps -> findRefs e <> mconcat (findRefs . snd <$> ps)
  ELet bs e ->
    let (names, exprs) = unzip $ splitBind <$> bs
        exprs' = e : exprs
    in S.unions (findRefs <$> exprs') S.\\ S.fromList names
  where splitBind (BindingImpl x e)   = (x,e)
        splitBind (BindingExpl x e _) = (x,e)


fresh :: Infer Type
fresh = get >>= \(x,s) -> TUnif x <$ put (x+1,s)

replace :: Map Text Type -> Type -> Type
replace subs = go
  where go (TApp x y) = TApp (go x) (go y)
        go (TName x) = TName x
        go (TVar x) = fromMaybe (TVar x) $ M.lookup x subs
        go (TUnif x) = TUnif x

applySubs :: Subs -> Type -> Type
applySubs (Subs subs) = go
  where go (TApp x y) = TApp (go x) (go y)
        go (TName x) = TName x
        go (TVar x) = TVar x
        go (TUnif x) = fromMaybe (TUnif x) $ M.lookup x subs


-- |Instantiates the given type scheme with fresh unification variables
-- and returns the resulting type
instantiate :: TypeScheme -> Infer Type
instantiate (TypeScheme unis t) =
  let unis' = S.toList unis
  in
    const fresh `mapM` unis' <&> \insts ->
      replace (M.fromList $ zip unis' insts) t

generalize :: Integer -> Type -> TypeScheme
generalize min t =
  let unifs = findUnifs t
      names = M.fromList $ zip (S.toList unifs) (fmap (\x -> "a" <> T.pack (show x)) [0..]) -- TODO FIXME XXX CONFLICTS?
  in TypeScheme (S.fromList $ M.elems names) $ applySubs (Subs $ M.map TVar names) t
  where findUnifs (TApp l r) = findUnifs l <> findUnifs r
        findUnifs (TUnif i) = S.singleton i
        findUnifs _ = S.empty

generalize' :: Integer -> Type -> Infer TypeScheme
generalize' min t = do
  s <- getSubs
  pure $ generalize min $ applySubs s t

lookupEnv :: Text -> Infer TypeScheme
lookupEnv x = asks (M.lookup x . envTypeEnv) >>= \case
  Nothing -> throwError $ TE_ $ "unknown ident " <> x
  Just t  -> pure t

localTypeEnv :: (TypeEnv -> TypeEnv) -> Infer a -> Infer a
localTypeEnv f = local (\e -> e { envTypeEnv = f $ envTypeEnv e })

tyContains :: Type -> Integer -> Bool
TApp l r `tyContains` i = l `tyContains` i || r `tyContains` i
TUnif x `tyContains` i = x == i
_ `tyContains` _ = False

getSubs :: Infer Subs
getSubs = gets snd

extendSubs :: Subs -> Infer ()
extendSubs s' = do
  (x,s) <- get
  put (x, s <> s')

-- }}}

-- Unification {{{

unify :: Type -> Type -> Infer ()
unify t0 t1 = do
  s <- getSubs
  u <- unify' (applySubs s t0) (applySubs s t1)
  extendSubs u
  where
    unify' :: Type -> Type -> Infer Subs

    unify' (TName x) (TName y)
      | x == y = pure mempty
      | otherwise = throwError $ TE_ "attempted to unify different concrete types"

    unify' (TApp l0 r0) (TApp l1 r1) = do
      s0 <- unify' l0 l1
      s1 <- unify' (applySubs s0 r0) (applySubs s0 r1)
      pure $ s0 <> s1

    unify' (TUnif x) t
      | t == TUnif x = pure mempty
      | t `tyContains` x = throwError $ TE_ "infinite type"
      | otherwise = pure $ Subs $ M.singleton x t -- TODO: kind check!!

    unify' t (TUnif x) = unify' (TUnif x) t

    unify' t0 t1 = throwError $ TE_ $ T.pack $ "cannot unify " <> show t0 <> " and " <> show t1

-- }}}

infer :: Expr -> Infer Type
infer = \case
  EName x -> lookupEnv x >>= instantiate

  ENatLit _ -> pure $ TName "Nat"

  EAppl ef ex -> do
    tf <- infer ef
    tx <- infer ex
    tr <- fresh
    unify tf (tx `tArrow` tr)
    pure tr

  ELambda x b -> do
    tx <- fresh
    tb <- localTypeEnv (M.insert x (TypeScheme S.empty tx)) $ infer b
    pure $ tx `tArrow` tb

  ELet bs e -> do
    env <- inferBindings bs
    localTypeEnv (M.union env) $ infer e

  ECase e cs -> _

inferScheme :: Expr -> Infer TypeScheme
inferScheme e = do
  firstTyVar <- gets fst
  t <- infer e
  s <- getSubs
  pure $ generalize firstTyVar $ applySubs s t

inferGroup :: TypeEnv -> [(Text, Expr)] -> Infer TypeEnv
inferGroup env binds = localTypeEnv (M.union env) $ do
  groupEnv <- foldM (\env (x,_) -> do { t <- fresh; pure $ M.insert x (TypeScheme S.empty t) env }) M.empty binds

  firstTyVar <- gets fst

  inferred <- localTypeEnv (M.union groupEnv)
    $ traverse (\(x,e) -> do { t <- infer e; pure (x,t) }) binds

  zipWithM unify ((\(TypeScheme _ t) -> t) <$> M.elems groupEnv) (snd <$> inferred)

  inferred' <- mapM (\(x,t) -> do { ts <- generalize' firstTyVar t; pure (x, ts) }) inferred

  pure $ env <> M.fromList inferred'

inferBindings :: [Binding] -> Infer TypeEnv
inferBindings bs = do
  let (impls, expls) = traceShowId $ partitionEithers $ bs <&> \case
        BindingImpl x e   -> Left (x,e)
        BindingExpl x e t -> Right (x,e,t)
        
      -- Find all the references in the implicit bindings
      refs = impls <&> \(x,e) -> ((x,e), x, S.toList $ findRefs e)

      -- This gives us a list of binding groups in the order they must be
      -- inferred.
      groups = traceShowId $ G.flattenSCC <$> G.stronglyConnComp refs

      -- All explicitly typed bindings need to be present in the type
      -- env for inference of implicitly typed bindings
      envExpl = foldr (\(x,_,t) -> M.insert x t) M.empty expls

  envImpl <- foldM inferGroup envExpl groups

  -- Now we've inferred the implicitly typed bindings, we need to infer
  -- the types of explicitly typed bindings under this environment, and
  -- check they match the given type.
  
  let fullEnv = envImpl <> envExpl

  explsInferred <- localTypeEnv (M.union fullEnv)
    $ traverse inferScheme
    $ fmap (\(_,e,_) -> e) expls

  let valid = and $ zipWith fitsScheme explsInferred (fmap (\(_,_,t) -> t) expls)

  when (not valid) $ throwError $ TE_ "bad fitsscheme"

  pure fullEnv
