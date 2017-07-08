{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE PatternSynonyms #-}

module Cochis.Parser where

import Control.Applicative
import Control.Monad.Except
import GHC.Stack
import Language.Haskell.Exts.Simple
  ( Module, Decl, Exp, Pat, Type, KnownExtension(..) )
import qualified Language.Haskell.Exts.Simple as Hs
import Unbound.Generics.LocallyNameless

import Cochis.Parser.Patterns
import Cochis.Types

data ParseError = ParseError CallStack String String
  deriving Show

parseError
  :: (MonadError ParseError m, HasCallStack, Hs.Pretty l)
  => l -> String -> m a
parseError l = throwError . ParseError ?callStack (Hs.prettyPrint l)

type Name' = Hs.Name

parseMod :: String -> Either ParseError [(Name', E)]
parseMod = fromModule . Hs.fromParseResult . Hs.parseModuleWithMode mode
  where
    mode = Hs.defaultParseMode
      { Hs.extensions = fmap Hs.EnableExtension
          [ RankNTypes
          , ScopedTypeVariables
          , TypeApplications
          ]
      }

fromModule :: Module -> Either ParseError [(Name', E)]
fromModule (Hs.Module _ _ _ ds) = traverse fromDecl ds
fromModule _ = error "Should not happen"

fromDecl :: Decl -> Either ParseError (Name', E)
fromDecl (HsDecl name e) = fmap ((,) name) (runFreshMT (fromExp e))
fromDecl d = parseError d "Unsupported declaration"

fromExp :: (Fresh m, MonadError ParseError m) => Exp -> m E
fromExp (Hs.Paren e) = fromExp e
fromExp (HsIQuery t) = fmap IQuery (fromType t)
fromExp (HsTAbs as e) = desugar as
  where
    desugar [] = fromExp e
    desugar (a : as) = do
      e' <- desugar as
      return (TAbs (bind (fromName a) e'))
fromExp e_@(Hs.Lambda p e) = desugar p
  where
    desugar [] = fromExp e
    desugar (p : ps)
      | Hs.PatTypeSig (Hs.PVar v) t <- unParen p = do
          e' <- desugar ps
          t' <- fromType t
          return (Abs (bind (fromName v, Embed t') e'))
      | otherwise = parseError e_ "Invalid pattern"
fromExp (HsIAbs t e) = do
  t' <- fromType t
  e' <- fromExp e
  return (IAbs t' e')
fromExp (HsIApp e0 e1) = do
  e1 <- fromExp e1
  e0 <- fromExp e0
  return (IApp e0 e1)
fromExp (HsTApp e t)  = liftA2 TApp (fromExp e) (fromType t)
fromExp (Hs.App e1 e2) = liftA2 App (fromExp e1) (fromExp e2)
fromExp (HsVar v) = return (Var (fromName v))
fromExp e = error (Hs.prettyPrint e)

fromType :: (Fresh m, MonadError ParseError m) => Type -> m T
fromType (Hs.TyParen t) = fromType t
fromType (Hs.TyVar v) = return (TyVar (fromName v))
fromType (Hs.TyFun t0 t1) = liftA2 TyFun (fromType t0) (fromType t1)
fromType (Hs.TyForall (Just as') Nothing t) | Just as <- unkinded as' = desugar as
  where
    desugar [] = fromType t
    desugar (a : as) = do
      t' <- desugar as
      return (TyAll (bind (fromName a) t'))
fromType (HsTyIFun t0 t1) =
  liftA2 TyIFun (fromType t0) (fromType t1)
fromType (HsTyCon c) = return (TyCon c)
fromType t = error (Hs.prettyPrint t)

unParen :: Pat -> Pat
unParen (Hs.PParen p) = unParen p
unParen p = p

fromName :: Hs.Name -> Name a
fromName = string2Name . Hs.prettyPrint
