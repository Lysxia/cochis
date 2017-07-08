{-# LANGUAGE FlexibleContexts #-}

module Cochis.Printer where

import Control.Applicative
import Language.Haskell.Exts.Simple hiding
  (Name, name, Var, App, TyVar, IAbs)
import qualified Language.Haskell.Exts.Simple as Hs
import Unbound.Generics.LocallyNameless

import Cochis.Types

type Name' = Hs.Name

printMod :: [(Name', E)] -> String
printMod = prettyPrint . toModule

toModule :: [(Name', E)] -> Module
toModule ds = Module Nothing [] [] (fmap toDecl ds)

toDecl :: (Name', E) -> Decl
toDecl (name, e) = PatBind (PVar name) (UnGuardedRhs (runFreshM (toExp e))) Nothing

toExp :: Fresh m => E -> m Exp
toExp (Abs b) = do
  ((v, Embed t), e) <- unbind b
  e' <- toExp e
  t' <- toType t
  return (Paren (Hs.Lambda [PParen (PatTypeSig (PVar (toName v)) t')] e'))
toExp (App e1 e2) = liftA2 Hs.App (toExp e1) (toExp e2)
toExp (Var v) = return (Hs.Var (UnQual (toName v)))
toExp (TAbs b) = do
  (a, e) <- unbind b
  e' <- toExp e
  return (Paren (Hs.ExpTypeSig
    e'
    (TyForall (Just [UnkindedVar (toName a)]) Nothing (TyWildCard Nothing))))
toExp (TApp e t) = do
  e' <- toExp e
  t' <- toType t
  return (Hs.App e' (Hs.TypeApp t'))
toExp (IQuery t) = do
  t' <- toType t
  return (Hs.ExpTypeSig ExprHole t')
toExp (IAbs t e) = do
  t' <- toType t
  e' <- toExp e
  return (Hs.App (Hs.App (Hs.Var (UnQual (Ident "implicit"))) (TypeApp t')) e')
toExp (IApp e0 e1) = do
  e0' <- toExp e0
  e1' <- toExp e1
  return (Hs.App (Hs.App (Hs.Var (UnQual (Ident "with"))) e1') e0')

toType :: Fresh m => T -> m Type
toType (TyVar v) = return (Hs.TyVar (toName v))
toType t = error (show t)

toName :: Name a -> Hs.Name
toName = Ident . name2String
