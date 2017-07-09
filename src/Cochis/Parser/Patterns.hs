{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE ViewPatterns #-}

module Cochis.Parser.Patterns where

import Language.Haskell.Exts.Simple

pattern HsVar :: Name -> Exp
pattern HsVar v = Var (UnQual v)

pattern HsTAbs :: [Name] -> Exp -> Exp
pattern HsTAbs as e =
  ExpTypeSig e (TyForall (Just (Unkinded as)) Nothing (TyWildCard Nothing))

pattern Unkinded :: [Name] -> [TyVarBind]
pattern Unkinded as <- (unkinded -> Just as)
  where Unkinded as = fmap UnkindedVar as

unkinded :: [TyVarBind] -> Maybe [Name]
unkinded = traverse unkinded'
  where
    unkinded' (UnkindedVar a) = Just a
    unkinded' _ = Nothing
    
pattern HsTApp :: Exp -> Type -> Exp
pattern HsTApp e t = App e (TypeApp' t)

pattern HsIQuery :: Type -> Exp
pattern HsIQuery t = ExpTypeSig ExprHole t

pattern HsIApp :: Exp -> Exp -> Exp
pattern HsIApp e0 e1 = App (App (LitVar "with") e1) e0

pattern HsIAbs :: Type -> Exp -> Exp
pattern HsIAbs t e = App (App (LitVar "implicit") (TypeApp' t)) e

pattern HsTyIFun :: Type -> Type -> Type
pattern HsTyIFun t0 t1 = TyInfix t0 (LitSym "~>") t1

pattern HsTyCon :: String -> Type
pattern HsTyCon c = TyCon (UnQual (Ident c))

pattern HsDecl :: Name -> Exp -> Decl
pattern HsDecl name e = PatBind (PVar name) (UnGuardedRhs e) Nothing

pattern LitVar :: String -> Exp
pattern LitVar s = HsVar (Ident s)

pattern LitSym :: String -> QName
pattern LitSym s = UnQual (Symbol s)

-- With automatic parentheses as a constructor.
pattern TypeApp' :: Type -> Exp
pattern TypeApp' t <- TypeApp t
  where TypeApp' t = TypeApp (case t of
          TyVar _ -> t
          TyCon _ -> t
          _ -> TyParen t)
