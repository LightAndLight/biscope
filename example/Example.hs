{-# language DeriveFunctor, DeriveFoldable, DeriveTraversable #-}
{-# language FlexibleInstances, MultiParamTypeClasses #-}
{-# language TemplateHaskell #-}
module Main where

import Bound.Scope (Scope, toScope)
import Bound.TH (makeBound)
import Bound.Var (Var(..))
import Control.Monad (ap)
import Data.Bifunctor (Bifunctor(..))
import Data.Deriving (deriveEq1, deriveShow1, deriveEq2, deriveShow2)
import Data.Functor.Classes (eq1, showsPrec1)

import Biscope
import Bisubst.Class

data Kind ki
  = KindVar ki
  | KindApp (Kind ki) (Kind ki)
  | KindArr
  | KindType
  deriving (Functor, Foldable, Traversable)
makeBound ''Kind
deriveEq1 ''Kind
deriveShow1 ''Kind

instance Eq ki => Eq (Kind ki) where; (==) = eq1
instance Show ki => Show (Kind ki) where; showsPrec = showsPrec1

data Ty ki ty
  = TyVar ty
  | TyApp (Ty ki ty) (Ty ki ty)
  | TyForall (Maybe (Kind ki)) (Scope () (Ty ki) ty)
  | TyExists (Maybe (Kind ki)) (Scope () (Ty ki) ty)
  | TyArr
  | TyCtor String
  deriving (Functor, Foldable, Traversable)
makeBound ''Ty
deriveEq1 ''Ty
deriveShow1 ''Ty

instance (Eq ki, Eq ty) => Eq (Ty ki ty) where; (==) = eq1
instance (Show ki, Show ty) => Show (Ty ki ty) where; showsPrec = showsPrec1

instance Bifunctor Ty where; bimap = bisubstBimapDefault
instance Bisubst Ty Kind where
  bireturn = TyVar
  bisubst f g ty =
    case ty of
      TyVar a -> g a
      TyApp a b -> TyApp (bisubst f g a) (bisubst f g b)
      TyForall a b -> TyForall ((>>= f) <$> a) (bisubstScope f g b)
      TyExists a b -> TyExists ((>>= f) <$> a) (bisubstScope f g b)
      TyArr -> TyArr
      TyCtor a -> TyCtor a

data Tm tyf ty tm
  = TmVar tm
  | TmAnn (Tm tyf ty tm) (tyf ty)

  -- Value abstraction with optional annotation (lowercase lambda)
  | TmLamTm (Maybe (tyf ty)) (Scope () (Tm tyf ty) tm)
  -- Value application
  | TmAppTm (Tm tyf ty tm) (Tm tyf ty tm)

  -- Type abstraction (uppercase lambda)
  | TmLamTy (Biscope1 () tyf (Tm tyf) ty tm)
  -- Type application
  | TmAppTy (Tm tyf ty tm) (tyf ty)

  -- Existential introduction
  | TmPack (tyf ty) (Tm tyf ty tm)
  -- Existential elimination
  | TmOpen (Tm tyf ty tm) (Biscope2 () () tyf (Tm tyf) ty tm)
  deriving (Functor, Foldable, Traversable)

instance Monad tyf => Bifunctor (Tm tyf) where; bimap = bisubstBimapDefault
instance Monad tyf => Bisubst (Tm tyf) tyf where
  bireturn = TmVar

  bisubst f g tm =
    case tm of
      TmVar a -> g a
      TmAnn a b -> TmAnn (bisubst f g a) (b >>= f)
      TmLamTm a b -> TmLamTm ((>>= f) <$> a) (bisubstScope f g b)
      TmAppTm a b -> TmAppTm (bisubst f g a) (bisubst f g b)
      TmLamTy s -> TmLamTy $ bisubstBiscope1 f g s
      TmAppTy a b -> TmAppTy (bisubst f g a) (b >>= f)
      TmPack a b -> TmPack (a >>= f) (bisubst f g b)
      TmOpen a b -> TmOpen (bisubst f g a) (bisubstBiscope2 f g b)
instance Monad tyf => Applicative (Tm tyf ty) where; pure = return; (<*>) = ap
instance Monad tyf => Monad (Tm tyf ty) where
  return = bireturn; (>>=) a f = bisubst pure f a

id_ :: Tm (Ty ki) ty tm
id_ =
  TmLamTy $ toBiscope1 $
  TmLamTm (Just $ TyVar (B ())) $ toScope $
  TmAnn (TmVar $ B ()) (TyVar $ B ())

main :: IO ()
main = do
  print id_
