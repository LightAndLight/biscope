{-# language FlexibleInstances, MultiParamTypeClasses #-}
{-# language QuantifiedConstraints #-}
{-# language TemplateHaskell #-}
module Biscope
  ( -- * @Biscope1@
    Biscope1(..)
  , toBiscope1
  , fromBiscope1
    -- * Substitution
  , Bisubst(..)
  , bisubstBiscope1
  , bisubstScope
  , substBiscope1
    -- * Abstraction
  , absBiscope1
  , abs1Biscope1
    -- * Instantiation
  , instBiscope1
  , inst1Biscope1
    -- * @Biscope2@
  , Biscope2(..)
  , toBiscope2
  , fromBiscope2
  )
where

import Bound.Scope
import Bound.Var
import Control.Monad
import Data.Bifunctor
import Data.Bifoldable
import Data.Bitraversable
import Data.Deriving
import Data.Functor.Classes

import Bisubst.Class

newtype Biscope1 b f g a a' = Biscope1 { unBiscope1 :: g (Var b (f a)) a' }
deriveEq2 ''Biscope1
deriveShow2 ''Biscope1
deriveOrd2 ''Biscope1

instance (Eq b, Eq1 f, Eq2 g, Eq a) => Eq1 (Biscope1 b f g a) where
  liftEq = liftEq2 (==)

instance (Eq b, Eq1 f, Eq2 g, Eq a, Eq a') => Eq (Biscope1 b f g a a') where
  (==) = eq1

instance (Show b, Show1 f, Show2 g, Show a) => Show1 (Biscope1 b f g a) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

instance (Show b, Show1 f, Show2 g, Show a, Show a') => Show (Biscope1 b f g a a') where
  showsPrec = showsPrec1

instance (Ord b, Ord1 f, Ord2 g, Ord a) => Ord1 (Biscope1 b f g a) where
  liftCompare = liftCompare2 compare

instance (Ord b, Ord1 f, Ord2 g, Ord a, Ord a') => Ord (Biscope1 b f g a a') where
  compare = compare

instance (forall x. Functor (g x)) => Functor (Biscope1 b f g a) where
  fmap f (Biscope1 s) = Biscope1 $ fmap f s

instance (forall x. Foldable (g x)) => Foldable (Biscope1 b f g a) where
  foldMap f (Biscope1 s) = foldMap f s

instance (forall x. Traversable (g x)) => Traversable (Biscope1 b f g a) where
  traverse f (Biscope1 s) = Biscope1 <$> traverse f s

instance (Functor f, Bifunctor g) => Bifunctor (Biscope1 b f g) where
  bimap f g (Biscope1 s) = Biscope1 $ bimap (fmap (fmap f)) g s

instance (Foldable f, Bifoldable g) => Bifoldable (Biscope1 b f g) where
  bifoldMap f g (Biscope1 s) = bifoldMap (foldMap (foldMap f)) g s

instance (Traversable f, Bitraversable g) => Bitraversable (Biscope1 b f g) where
  bitraverse f g (Biscope1 s) = Biscope1 <$> bitraverse (traverse (traverse f)) g s

instance (Bifunctor g, forall x. Monad (g x)) => Applicative (Biscope1 b f g a) where
  pure = return
  (<*>) = ap

instance (Bifunctor g, forall x. Monad (g x)) => Monad (Biscope1 b f g a) where
  return = Biscope1 . return
  (>>=) (Biscope1 s) f = Biscope1 (unBiscope1 . f =<< s)

instance (Monad f, Bisubst g f) => Bisubst (Biscope1 b f g) f where
  bireturn = Biscope1 . bireturn
  bisubst f g (Biscope1 s) =
    Biscope1 $
    bisubst
      (unvar (return . B) (fmap (F . return) . f =<<))
      (unBiscope1 . g)
      s

substBiscope1 ::
  Bisubst g f =>
  (tm -> g ty tm') ->
  Biscope1 b f g ty tm ->
  Biscope1 b f g ty tm'
substBiscope1 f =
  Biscope1 .
  bisubst return (bimap (F . return) id . f) .
  unBiscope1

bisubstBiscope1 ::
  Bisubst g f =>
  (ty -> f ty') ->
  (tm -> g ty' tm') ->
  Biscope1 b f g ty tm ->
  Biscope1 b f g ty' tm'
bisubstBiscope1 f g =
  Biscope1 .
  bisubst
    (unvar (return . B) (fmap (F . return) . f =<<))
    (bimap (F . return) id . g) .
  unBiscope1

absBiscope1 :: Bisubst g f => (a -> Maybe b) -> g a a' -> Biscope1 b f g a a'
absBiscope1 f =
  Biscope1 .
  bisubst
    (\a -> maybe (return . F $ return a) (return . B) $ f a)
    bireturn

abs1Biscope1 :: (Eq a, Bisubst g f) => a -> g a a' -> Biscope1 () f g a a'
abs1Biscope1 a = absBiscope1 (\x -> if x == a then Just () else Nothing)

instBiscope1 :: Bisubst g f => f a -> Biscope1 b f g a a' -> g a a'
instBiscope1 a (Biscope1 s) = bisubst (unvar (const a) id) bireturn s

inst1Biscope1 :: Bisubst g f => f a -> Biscope1 () f g a a' -> g a a'
inst1Biscope1 = instBiscope1

toBiscope1 :: Bisubst g f => g (Var b a) a' -> Biscope1 b f g a a'
toBiscope1 = Biscope1 . bimap (fmap return) id

fromBiscope1 :: Bisubst g f => Biscope1 b f g a a' -> g (Var b a) a'
fromBiscope1 = bisubst (unvar (return . B) (fmap F)) bireturn . unBiscope1

bisubstScope ::
  Bisubst g f =>
  (ty -> f ty') ->
  (tm -> g ty' tm') ->
  Scope b (g ty) tm ->
  Scope b (g ty') tm'
bisubstScope f g =
  Scope .
  bisubst
    f
    (unvar (bireturn . B) (bimap id (F . bireturn) . bisubst f g)) .
  unscope


newtype Biscope2 b b' f g a a'
  = Biscope2 { unBiscope2 :: g (Var b (f a)) (Var b' (g (Var b (f a)) a')) }
deriveEq2 ''Biscope2
deriveShow2 ''Biscope2
deriveOrd2 ''Biscope2

toBiscope2 ::
  Bisubst g f =>
  g (Var b a) (Var b' a') ->
  Biscope2 b b' f g a a'
toBiscope2 = Biscope2 . bimap (fmap return) (fmap bireturn)

fromBiscope2 ::
  Bisubst g f =>
  Biscope2 b b' f g a a' ->
  g (Var b a) (Var b' a')
fromBiscope2 =
  bisubst
    unwrap
    (unvar (bireturn . B) (bisubst unwrap (bireturn . F))) .
    unBiscope2
  where
    unwrap = unvar (return . B) (fmap F)