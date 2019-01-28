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

data Tm f ki ty tm
  = TmVar tm
  | TmApp (Tm f ki ty tm) (Tm f ki ty tm)
  | TmLamTm (Maybe (f ki ty)) (Scope () (Tm t ki ty) tm)
  | TmLamTy (Biscope () (f ki) Tm ty tm)
  | TmPack (f ki ty) (Tm f ki ty tm)
  | TmOpen (Tm f ki ty tm) _
  | TyArr
  | TyCtor String
  deriving (Functor, Foldable, Traversable)
deriveBifunctor ''Ty

main :: IO ()
main = pure ()