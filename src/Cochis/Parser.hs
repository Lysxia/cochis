{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}

module Cochis.Parser where

import Control.Applicative
import Control.Monad.Except
import GHC.Stack
import Language.Haskell.Exts.Simple hiding
  (Name, Var, App, TyVar, IAbs)
import qualified Language.Haskell.Exts.Simple as Hs
import Unbound.Generics.LocallyNameless

import Cochis.Types

data ParseError = ParseError CallStack String
  deriving Show

parseError :: (MonadError ParseError m, HasCallStack) => String -> m a
parseError = throwError . ParseError ?callStack

type Name' = Hs.Name

parseMod :: String -> Either ParseError [(Name', E)]
parseMod = fromModule . fromParseResult . parseModuleWithMode mode
  where
    mode = defaultParseMode
      { extensions = fmap EnableExtension
          [ RankNTypes
          , ScopedTypeVariables
          , TypeApplications
          ]
      }

fromModule :: Module -> Either ParseError [(Name', E)]
fromModule (Module _ _ _ ds) = traverse fromDecl ds
fromModule _ = error "Should not happen"

fromDecl :: Decl -> Either ParseError (Name', E)
fromDecl (PatBind (PVar name) (UnGuardedRhs e) Nothing) = fmap ((,) name) (runFreshMT (fromExp e))
fromDecl PatBind{} = parseError "Bad definition"
fromDecl _ = parseError "Unsupported declaration"

fromExp :: (Fresh m, MonadError ParseError m) => Exp -> m E
fromExp (Hs.Paren e) = fromExp e
fromExp (Hs.ExpTypeSig ExprHole t) = fmap IQuery (fromType t)
fromExp (Hs.ExpTypeSig e (TyForall vs ctx t0))
  | Just [UnkindedVar a] <- vs, Nothing <- ctx, TyWildCard Nothing <- t0 = do
      e' <- fromExp e
      return (TAbs (bind (fromName a) e'))
  | otherwise = parseError ""
fromExp (Hs.Lambda p e) = desugar p
  where
    desugar [] = fromExp e
    desugar (p : ps)
      | PatTypeSig (PVar v) t <- unParen p = do
          e' <- desugar ps
          t' <- fromType t
          return (Abs (bind (fromName v, Embed t') e'))
      | otherwise = parseError "Invalid pattern"
fromExp (Hs.App (Hs.App (Hs.Var (UnQual (Ident "implicit"))) (TypeApp t)) e) = do
  t' <- fromType t
  e' <- fromExp e
  return (IAbs t' e')
fromExp (Hs.App (Hs.App (Hs.Var (UnQual (Ident "with"))) e1) e0) = do
  e1 <- fromExp e1
  e0 <- fromExp e0
  return (IApp e0 e1)
fromExp (Hs.App e (Hs.TypeApp t)) = liftA2 TApp (fromExp e) (fromType t)
fromExp (Hs.App e1 e2) = liftA2 App (fromExp e1) (fromExp e2)
fromExp (Hs.Var (UnQual v)) = return (Var (fromName v))
fromExp (Hs.Var _) = parseError "Qualified/Special name"
fromExp e = error (show e)

fromType :: (Fresh m, MonadError ParseError m) => Type -> m T
fromType (Hs.TyParen t) = fromType t
fromType (Hs.TyVar v) = return (TyVar (fromName v))
fromType t = error (show t)

unParen :: Pat -> Pat
unParen (PParen p) = unParen p
unParen p = p

fromName :: Hs.Name -> Name a
fromName = string2Name . prettyPrint
