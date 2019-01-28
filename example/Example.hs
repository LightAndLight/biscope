{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language TemplateHaskell #-}
module Main where

import Bound.Scope (Scope)
import Biscope (Biscope)
import Data.Bifunctor.TH (deriveBifunctor)

data Kind ki
  = KindVar ki
  | KindApp (Kind ki) (Kind ki)
  | KindArr
  | KindType
  deriving (Functor, Foldable, Traversable)

data Ty ki ty
  = TyVar ty
  | TyApp (Ty ki ty) (Ty ki ty)
  | TyForall (Maybe (Kind ki)) (Scope () (Ty ki) ty)
  | TyExists (Maybe (Kind ki)) (Scope () (Ty ki) ty)
  | TyArr
  | TyCtor String
  deriving (Functor, Foldable, Traversable)
deriveBifunctor ''Ty

data Tm f ty tm
  = TmVar tm
  | TmAnn (Tm f ty tm) (f ty)
  | TmApp (Tm f ty tm) (Tm f ty tm)

  -- Value abstraction with optional annotation (lowercase lambda)
  | TmLamTm (Maybe (f ty)) (Scope () (Tm f ty) tm)

  -- Type abstraction (uppercase lambda)
  | TmLamTy (Biscope () f Tm ty tm)

  -- Existential introduction
  | TmPack (f ty) (Tm f ty tm)

  -- Existential elimination
  | TmOpen (Tm f ty tm) (Biscope2 () () f Tm ty tm)
  deriving (Functor, Foldable, Traversable)
deriveBifunctor ''Ty

main :: IO ()
main = pure ()