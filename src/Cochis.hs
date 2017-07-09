{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ViewPatterns #-}

module Cochis where

import Control.Applicative
import Control.Monad
import Control.Monad.Except
import Control.Monad.Trans.Maybe
import Data.Bimap (Bimap)
import qualified Data.Bimap as Bimap
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics
import GHC.Stack
import Lens.Micro
import Unbound.Generics.LocallyNameless

import Cochis.Types

data TypeError = TypeError CallStack String String
  deriving Show

typeError
  :: (MonadError TypeError m, HasCallStack, Show l)
  => l -> String -> m a
typeError l = throwError . TypeError ?callStack (show l)

data Ctx
  = CtxNil
  | CtxT (Rebind (Name T) Ctx)
  | CtxE (Rebind (Name E, Embed T) Ctx)
  deriving (Show, Generic)

instance Alpha Ctx

type ICtx = [(Name E, T)]

newTVar :: Ctx -> Name T -> Ctx
newTVar CtxNil a = CtxT (rebind a CtxNil)
newTVar (CtxT (unrebind -> (a1, ctx))) a = CtxT (rebind a1 (newTVar ctx a))
newTVar (CtxE (unrebind -> (vt1, ctx))) a = CtxE (rebind vt1 (newTVar ctx a))

newEVar :: Ctx -> (Name E, Embed T) -> Ctx
newEVar CtxNil vt = CtxE (rebind vt CtxNil)
newEVar (CtxT (unrebind -> (a1, ctx))) vt = CtxT (rebind a1 (newEVar ctx vt))
newEVar (CtxE (unrebind -> (vt1, ctx))) vt = CtxE (rebind vt1 (newEVar ctx vt))

lookupEVar :: MonadError TypeError m => Ctx -> Name E -> m T
lookupEVar CtxNil v = typeError v "Unbound variable"
lookupEVar (CtxT (unrebind -> (_, ctx))) v = lookupEVar ctx v
lookupEVar (CtxE (unrebind -> ((v1, t1), ctx))) v
  | v1 == v = pure (unembed t1)
  | otherwise = lookupEVar ctx v

tyCtx :: Ctx -> [Name T]
tyCtx CtxNil = []
tyCtx (CtxT (unrebind -> (a1, ctx))) = a1 : tyCtx ctx
tyCtx (CtxE (unrebind -> (_, ctx))) = tyCtx ctx

typeCheck :: (MonadError TypeError m, Fresh m) => Ctx -> ICtx -> E -> m (E, T)
typeCheck ctx ictx e = case e of
  Var v -> fmap ((,) (Var v)) (lookupEVar ctx v)
  Abs b -> do
    (vt@(v, Embed t0), e1) <- unbind b
    assertClosedType e (tyCtx ctx) t0
    (e1_, t1) <- typeCheck (newEVar ctx vt) ictx e1
    t0_ <- translateType t0
    return (Abs (bind (v, embed t0_) e1_), TyFun t0 t1)
  App e0 e1 -> do
    (e0_, TyFun t1 t2) <- typeCheck ctx ictx e0
    (e1_, t1') <- typeCheck ctx ictx e1
    assertEqualTypes e t1 t1'
    return (App e0_ e1_, t2)
  TAbs b -> do
    (a0, e1) <- unbind b
    (e1_, t1) <- typeCheck (newTVar ctx a0) ictx e1
    return (TAbs (bind a0 e1_), TyAll (bind a0 t1))
  TApp e0 t1 -> do
    (e0_, TyAll b) <- typeCheck ctx ictx e0
    assertClosedType e (tyCtx ctx) t1
    (a1, t0) <- unbind b
    t1_ <- translateType t1
    return (TApp e0_ t1_, subst a1 t1 t0)
  IAbs t0 e1 -> do
    assertClosedType e (tyCtx ctx) t0
    unamb [] t0
    x <- fresh (string2Name "imp")
    (e1_, t1) <- typeCheck ctx ((x, t0) : ictx) e1
    t0_ <- translateType t0
    return (Abs (bind (x, embed t0_) e1_), TyIFun t0 t1)
  IApp e0 e1 -> do
    (e0_, TyIFun t1 t2) <- typeCheck ctx ictx e0
    (e1_, t1') <- typeCheck ctx ictx e1
    assertEqualTypes e t1 t1'
    return (App e0_ e1_, t2)
  IQuery t0 -> do
    assertClosedType e (tyCtx ctx) t0
    unamb [] t0
    e0_ <- resolve (Set.fromList (tyCtx ctx)) ictx t0
    return (e0_, t0)

typeCheck0 :: MonadError TypeError m => E -> m (E, T)
typeCheck0 = runFreshMT . typeCheck CtxNil []

-- We first open all implicit and type abstractions.
resolve
  :: (MonadError TypeError m, Fresh m)
  => Set (Name T)
  -- ^ Type variables in scope at the point of the query.
  -- To ensure coherence, we must check that no instantiation of these variables
  -- may change the outcome of the resolution.

  -> ICtx -> T -> m E
resolve as ictx t = case t of
  TyAll b -> do
    (a, t1) <- unbind b
    e1_ <- resolve as ictx t1
    return (TAbs (bind a e1_))
  TyIFun t0 t1 -> do
    x <- fresh (string2Name "res")
    e1_ <- resolve as ((x, t0) : ictx) t1
    t0_ <- translateType t0
    return (Abs (bind (x, Embed t0_) e1_))
  _ ->
    resolve' (resolve as ictx) as ictx t

-- We look for a match in the implicit context.
resolve'
  :: (MonadError TypeError m, Fresh m)
  => (T -> m E)    -- ^ Continuation to solve subgoals.
  -> Set (Name T)  -- ^ Type variables in scope at the point of the query.
  -> ICtx
  -> T             -- ^ Current goal.
  -> m E
resolve' k as ictx t = case ictx of
  [] -> typeError t "No match found."
  (v, t') : ictx' -> do
    subgoals <- match as t t' v
    case subgoals of
      Nothing -> resolve' k as ictx' t
      Just (e, ts) -> do
        s <- (traverse . traverse) k ts
        return (substs s e)

type Sub = Map (Name T) T

-- | Given @t, t'@, find @s@ such that @substs s t' `aeq` substs s t@,
-- with some more constraints on @s@...
unify
  :: (Alternative m, Fresh m)
  => Set (Name T)
  -> Set (Name T)
  -> T -> T -> m Sub
unify as es = unify' as es Bimap.empty

unify'
  :: (Alternative m, Fresh m)
  => Set (Name T)
  -> Set (Name T)

  -> Bimap (Name T) (Name T)
  -- ^ Name equivalence between @t@ and @t'@.
  -- Not sure whether 'unbind2' is supposed to generate equal names.

  -> T -> T -> m Sub
unify' as es nameEq t t' = case (t, t') of
  (TyAll b, TyAll b') -> do
    Just (a, t0, a', t0') <- unbind2 b b'
    let nameEq' = Bimap.insert a a' nameEq
    unify' as es nameEq' t0 t0'

  (TyIFun t0 t1, TyIFun t0' t1') ->
    unify2' as es nameEq (t0, t1) (t0', t1')

  (TyFun t0 t1, TyFun t0' t1') ->
    unify2' as es nameEq (t0, t1) (t0', t1')

  (TyCon c, TyCon c') | c == c' -> pure Map.empty

  (TyVar a, TyVar a')
    | a == a' -> return Map.empty
    | (a, a') `Bimap.pairMember` nameEq -> return Map.empty
    | a `Set.member` as ->
        if a' `Set.member` as then
          return (Map.singleton a (TyVar a'))
        else if a' `Set.member` es then
          return (Map.singleton a' (TyVar a))
        else
          empty
    | a `Set.member` es ->
        if a' `Set.member` as || a' `Set.member` es then
          return (Map.singleton a (TyVar a'))
        else
          empty

  (TyVar a, t) -> unifyVar' as es a t
  (t, TyVar a) -> unifyVar' as es a t

  _ -> empty

unify2'
  :: (Alternative m, Fresh m)
  => Set (Name T)
  -> Set (Name T)
  -> Bimap (Name T) (Name T)
  -> (T, T) -> (T, T) -> m Sub
unify2' as es nameEq (t0, t1) (t0', t1') = do
  s0 <- unify' as es nameEq t0 t0'
  let substs0 = substs_ s0
  s1 <- unify' as es nameEq (substs0 t1) (substs0 t1')
  return (fmap (substs_ s1) s0 `Map.union` s1)

substs_ :: Subst b a => Map (Name b) b -> a -> a
substs_ = substs . Map.toList

unifyVar'
  :: (Alternative m, Monad m, Alpha a)
  => Set (Name T) -> Set (Name T) -> Name T -> a -> m (Map (Name T) a)
unifyVar' as es a t
  | member a && all (\a' -> member a' && a /= a') (t ^.. fv) =
      return (Map.singleton a t)
  | otherwise = empty
  where
    member a = a `Set.member` as || a `Set.member` es

-- If the candidate matches, return @Just@ a list of subgoals.
-- If there is a potential incoherence, throw a type error.
-- Otherwise, return @Nothing@.
match
  :: (Fresh m, MonadError TypeError m)
  => Set (Name T)
  -> T  -- ^ Current goal.
  -> T  -- ^ Match candidate.
  -> Name E
  -> m (Maybe (E, [(Name E, T)]))
match as t t' v = runMaybeT (match' as [] [] t t' (Var v))

match'
  :: (Fresh m, MonadError TypeError m)
  => Set (Name T)   -- ^ Type variables in scope at the point of the query.
  -> [Name T]       -- ^ Unifiable type variables for the match candidate.
  -> [(Name E, T)]  -- ^ Subgoals generated by the match candidate.
  -> T              -- ^ Current goal.
  -> T              -- ^ Match candidate.
  -> E              -- ^ Candidate translation.
  -> MaybeT m (E, [(Name E, T)])
match' as us subgs t t' e' = case t' of
  TyAll b -> do
    (u, t1') <- unbind b
    match' as (u : us) subgs t t1' (TApp e' (TyVar u))
  TyIFun t0 t1 -> do
    -- In the paper M-IApp adds t0 to ictx (rho1 to Gamma)???
    x <- fresh (string2Name "mat")
    match' as us ((x, t0) : subgs) t t1 (App e' (Var x))
  _ -> do
    s <- unify as (Set.fromList us) t t'
    unless (all (idem s) as) $ typeError t "Incoherent match."
    return (substs_ s e', [(x, substs_ s t_) | (x, t_) <- subgs])

-- | Check whether a substitution maps a variable to itself.
idem :: Sub -> Name T -> Bool
idem s a = case Map.lookup a s of
  Nothing -> True
  Just (TyVar a') -> a == a'
  Just _ -> False

monoType :: T -> Bool
monoType t = case t of
  TyFun t0 t1 -> monoType t0 && monoType t1
  TyVar _ -> True
  TyCon _ -> True
  _ -> False

unamb :: (MonadError TypeError m, Fresh m) => [Name T] -> T -> m ()
unamb as t = case t of
  TyAll b -> do
    (a0, t1) <- unbind b
    unamb (a0 : as) t1
  TyIFun t0 t1 -> do
    unamb [] t0
    unamb as t1
  t ->
    unless (Set.fromList as `Set.isSubsetOf` Set.fromList (t ^.. fv)) $
      typeError t "Ambiguous type."

closedType :: [Name T] -> T -> Bool
closedType as t = Set.fromList (t ^.. fv) `Set.isSubsetOf` Set.fromList as

translateType :: Fresh m => T -> m T
translateType t = case t of
  TyAll b -> do
    (a0, t1) <- unbind b
    t1_ <- translateType t1
    return (TyAll (bind a0 t1_))
  TyFun t0 t1 -> liftA2 TyFun (translateType t0) (translateType t1)
  TyIFun t0 t1 -> liftA2 TyFun (translateType t0) (translateType t1)
  TyVar a -> return (TyVar a)
  TyCon c -> return (TyCon c)

assertClosedType
  :: (Show e, MonadError TypeError m)
  => e -> [Name T] -> T -> m ()
assertClosedType e as t =
  unless (closedType as t) $ typeError e "Type has unbound variables."

assertEqualTypes
  :: (Show e, MonadError TypeError m)
  => e -> T -> T -> m ()
assertEqualTypes e t1 t1' =
  unless (t1 `aeq` t1') $ typeError e "Mismatched types."
