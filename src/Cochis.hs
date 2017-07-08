{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE ViewPatterns #-}

module Cochis where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Maybe
import Data.Foldable
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import GHC.Generics
import Lens.Micro
import Unbound.Generics.LocallyNameless

import Cochis.Types

data Ctx
  = CtxNil
  | CtxT (Rebind (Name T) Ctx)
  | CtxE (Rebind (Name E, Embed T) Ctx)
  deriving (Show, Generic)

instance Alpha Ctx

type ICtx = [T]

newTVar :: Ctx -> Name T -> Ctx
newTVar CtxNil a = CtxT (rebind a CtxNil)
newTVar (CtxT (unrebind -> (a1, ctx))) a = CtxT (rebind a1 (newTVar ctx a))
newTVar (CtxE (unrebind -> (vt1, ctx))) a = CtxE (rebind vt1 (newTVar ctx a))

newEVar :: Ctx -> (Name E, Embed T) -> Ctx
newEVar CtxNil vt = CtxE (rebind vt CtxNil)
newEVar (CtxT (unrebind -> (a1, ctx))) vt = CtxT (rebind a1 (newEVar ctx vt))
newEVar (CtxE (unrebind -> (vt1, ctx))) vt = CtxE (rebind vt1 (newEVar ctx vt))

lookupEVar :: Alternative m => Ctx -> Name E -> m (Embed T)
lookupEVar CtxNil _ = empty
lookupEVar (CtxT (unrebind -> (_, ctx))) v = lookupEVar ctx v
lookupEVar (CtxE (unrebind -> ((v1, t1), ctx))) v
  | v1 == v = pure t1
  | otherwise = lookupEVar ctx v

tyCtx :: Ctx -> [Name T]
tyCtx CtxNil = []
tyCtx (CtxT (unrebind -> (a1, ctx))) = a1 : tyCtx ctx
tyCtx (CtxE (unrebind -> (_, ctx))) = tyCtx ctx

typeCheck :: (Alternative m, Fresh m) => Ctx -> ICtx -> E -> m T
typeCheck ctx ictx e = case e of
  Var v -> fmap unembed (lookupEVar ctx v)
  Abs b -> do
    (vt@(_, Embed t0), e1) <- unbind b
    guard (closedType (tyCtx ctx) t0)
    t1 <- typeCheck (newEVar ctx vt) ictx e1
    return (TyFun t0 t1)
  App e0 e1 -> do
    TyFun t1 t2 <- typeCheck ctx ictx e0
    t1' <- typeCheck ctx ictx e1
    guard (t1 `aeq` t1')
    return t2
  TAbs b -> do
    (a0, e1) <- unbind b
    t1 <- typeCheck (newTVar ctx a0) ictx e1
    return (TyAll (bind a0 t1))
  TApp e0 t1 -> do
    TyAll b <- typeCheck ctx ictx e0
    guard (closedType (tyCtx ctx) t1)
    (a1, t0) <- unbind b
    return (subst a1 t1 t0)
  IAbs t0 e1 -> do
    guard (closedType (tyCtx ctx) t0)
    unamb [] t0
    t1 <- typeCheck ctx (t0 : ictx) e1
    return (TyIFun t0 t1)
  IApp e0 e1 -> do
    TyIFun t1 t2 <- typeCheck ctx ictx e0
    t1' <- typeCheck ctx ictx e1
    guard (t1 `aeq` t1')
    return t2
  IQuery t0 -> do
    guard (closedType (tyCtx ctx) t0)
    unamb [] t0
    resolve (tyCtx ctx) ictx t0
    return t0

typeCheck0 :: E -> Maybe T
typeCheck0 = runFreshMT . typeCheck CtxNil []

-- | In the paper, the stable rule seems to be using a type variable
-- environment @as@ which remains constant.
resolve :: (Alternative m, Fresh m) => [Name T] -> ICtx -> T -> m ()
resolve as ictx t = case t of
  TyAll b -> do
    (_, t1) <- unbind b
    resolve as ictx t1
  TyIFun t0 t1 ->
    resolve as (t0 : ictx) t1
  _ ->
    resolve' (resolve as ictx) as ictx t

resolve'
  :: (Alternative m, Fresh m)
  => (T -> m ())
  -> [Name T]
  -> ICtx
  -> T
  -> m ()
resolve' k as ictx t = case ictx of
  [] -> empty
  t' : ictx' -> do
    subgoals <- runMaybeT (match t' t)
    case subgoals of
      Nothing -> resolve' k as ictx' t
      Just (s, ts) -> do
        guard (all self (Map.toList s))  -- Check that the substitution is trivial.
        for_ ts k
  where
    self (a, TyVar a') | a == a' = True
    self _ = False

type Sub = Map (Name T) T

-- | Given @t, t'@, find @s@ such that @substs s t `aeq` t'@.
unify :: (Alternative m, Fresh m) => T -> T -> m Sub
unify = unify' Map.empty

unify'
  :: (Alternative m, Fresh m)
  => Map (Name T) (Name T) -> T -> T -> m Sub
unify' rename (TyAll b) (TyAll b') = do
  Just (a, t, a', t') <- unbind2 b b'
  unify' (Map.insert a a' rename) t t'
unify' rename (TyIFun t0 t1) (TyIFun t0' t1') = do
  s0 <- unify' rename t0 t0'
  s1 <- unify' rename t1 t1'
  mergeSubWith (\u0 u1 -> guard (u0 `aeq` u1) *> pure u0) s0 s1
unify' rename (TyFun t0 t1) (TyFun t0' t1') = do
  s0 <- unify' rename t0 t0'
  s1 <- unify' rename t1 t1'
  mergeSubWith (\u0 u1 -> guard (u0 `aeq` u1) *> pure u0) s0 s1
unify' rename (TyVar a) t'
  | Just a' <- Map.lookup a rename =
      case t' of
        TyVar a0' | a' == a0' -> pure Map.empty
        _ -> empty
  | closed = pure (Map.singleton a t')
  | otherwise = empty
  where
    closed = Set.null
      (Set.intersection
        (Set.fromList (Map.elems rename))
        (Set.fromList (t' ^.. fv)))
unify' _ (TyCon c) (TyCon c') | c == c' = pure Map.empty
unify' _ _ _ = empty

mergeSubWith :: (Ord k, Applicative f) => (a -> a -> f a) -> Map k a -> Map k a -> f (Map k a)
mergeSubWith m as as' =
  fmap Map.fromAscList (mergeWith m (Map.toAscList as) (Map.toAscList as'))

mergeWith :: (Ord k, Applicative f) => (a -> a -> f a) -> [(k, a)] -> [(k, a)] -> f [(k, a)]
mergeWith _ [] as = pure as
mergeWith _ as [] = pure as
mergeWith m aas0@((k0, a0) : as0) aas1@((k1, a1) : as1) = case compare k0 k1 of
  EQ -> liftA2 (\a as -> (k0, a) : as) (m a0 a1) (mergeWith m as0 as1)
  LT -> fmap ((k0, a0) :) (mergeWith m as0 aas1)
  GT -> fmap ((k1, a1) :) (mergeWith m aas0 as1)

match :: (Alternative m, Fresh m) => T -> T -> m (Sub, [T])
match t' t = case t' of
  TyAll b -> do
    (a, t1') <- unbind b
    (s, ts) <- match t1' t
    case Map.lookup a s of
      Nothing -> empty
      Just u -> guard (monoType u)
    return (Map.delete a s, ts)
  TyIFun t0 t1 -> do
    (s, ts) <- match t1 t  -- In the paper M-IApp adds t0 to ictx (rho1 to Gamma)???
    return (s, t0 : ts)
  t' -> do
    s <- unify t t'
    return (s, [])

monoType :: T -> Bool
monoType t = case t of
  TyFun t0 t1 -> monoType t0 && monoType t1
  TyVar _ -> True
  TyCon _ -> True
  _ -> False

unamb :: (Alternative m, Fresh m) => [Name T] -> T -> m ()
unamb as t = case t of
  TyAll b -> do
    (a0, t1) <- unbind b
    unamb (a0 : as) t1
  TyIFun t0 t1 -> do
    unamb [] t0
    unamb as t1
  t ->
    guard (Set.fromList as `Set.isSubsetOf` Set.fromList (t ^.. fv))

closedType :: [Name T] -> T -> Bool
closedType as t = Set.fromList (t ^.. fv) `Set.isSubsetOf` Set.fromList as
