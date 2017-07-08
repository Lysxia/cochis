{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Cochis.Types where

import GHC.Generics
import Unbound.Generics.LocallyNameless

data E
  = Var (Name E)
  | Abs (Bind (Name E, Embed T) E)
  | App E E
  | TAbs (Bind (Name T) E)
  | TApp E T
  | IQuery T
  | IAbs T E
  | IApp E E
  deriving (Show, Generic)

data T
  = TyVar (Name T)
  | TyFun T T
  | TyAll (Bind (Name T) T)
  | TyIFun T T
  deriving (Show, Generic)

instance Alpha E
instance Alpha T

instance Subst E E where
  isvar (Var v) = Just (SubstName v)
  isvar _ = Nothing

instance Subst E T where
  isvar _ = Nothing

instance Subst T T where
  isvar (TyVar v) = Just (SubstName v)
  isvar _ = Nothing


