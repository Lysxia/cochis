{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE PatternSynonyms #-}

module Cochis.Printer where

import Control.Applicative
import Language.Haskell.Exts.Simple
  ( Module, Decl, Exp, Type )
import qualified Language.Haskell.Exts.Simple as Hs
import Unbound.Generics.LocallyNameless

import Cochis.Parser.Patterns
import Cochis.Types

type Name' = Hs.Name

prettyPrint :: Hs.Pretty a => a -> String
prettyPrint = Hs.prettyPrint

printMod :: [(Name', E)] -> String
printMod = Hs.prettyPrint . toModule

toModule :: [(Name', E)] -> Module
toModule ds = Hs.Module Nothing [] [] (fmap toDecl ds)

toDecl :: (Name', E) -> Decl
toDecl (name, e) = HsDecl name (runLFreshM (toExp e))

toExp :: LFresh m => E -> m Exp
toExp (Abs b) = do
  lunbind b $ \((v, Embed t), e) -> do
    e' <- toExp e
    t' <- toType t
    return (Hs.Paren (Hs.Lambda
      [Hs.PParen (Hs.PatTypeSig (Hs.PVar (toName v)) t')]
      e'))
toExp (App e1 e2) = liftA2 Hs.App (toExp e1) (toExp e2)
toExp (Var v) = return (HsVar (toName v))
toExp (TAbs b) = do
  lunbind b $ \(a, e) -> do
    e' <- toExp e
    return (Hs.Paren (HsTAbs [toName a] e'))
toExp (TApp e t) = do
  e' <- toExp e
  t' <- toType t
  return (HsTApp e' t')
toExp (IQuery t) = fmap HsIQuery (toType t)
toExp (IAbs t e) = liftA2 HsIAbs (toType t) (toExp e)
toExp (IApp e0 e1) = liftA2 HsIApp (toExp e0) (toExp e1)

toType :: LFresh m => T -> m Type
toType (TyVar v) = return (Hs.TyVar (toName v))
toType (TyFun t0 t1) = toArrow Hs.TyFun t0 t1
toType (TyAll b) = do
  lunbind b $ \(a, t) -> do
    t' <- toType t
    return (Hs.TyForall (Just [Hs.UnkindedVar (toName a)]) Nothing t')
toType (TyIFun t0 t1) = toArrow HsTyIFun t0 t1
toType (TyCon c) = return (HsTyCon c)

toArrow :: LFresh m => (Type -> Type -> b) -> T -> T -> m b
toArrow f t0 t1 = do
  t0_ <- toType t0
  let
    t0' = case t0 of
      TyVar _ -> t0_
      TyCon _ -> t0_
      _ -> Hs.TyParen t0_
  t1' <- toType t1
  return (f t0' t1')

toName :: Name a -> Hs.Name
toName = Hs.Ident . show
