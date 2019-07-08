{-# language FlexibleContexts #-}
{-# language FlexibleInstances, MultiParamTypeClasses #-}
{-# language KindSignatures #-}
{-# language QuantifiedConstraints #-}
{-# language TemplateHaskell #-}
{-# language TypeFamilies #-}
module Biscope
  ( Bisubst(..)
    -- * @BiscopeL@
  , BiscopeL(..)
  , toBiscopeL
  , fromBiscopeL
    -- ** Substitution
  , bisubstBiscopeL
  , substBiscopeL
    -- ** Abstraction
  , absBiscopeL
  , abs1BiscopeL
    -- ** Instantiation
  , instBiscopeL
  , inst1BiscopeL
    -- * @BiscopeR@
  , BiscopeR(..)
  , toBiscopeR
  , fromBiscopeR
    -- ** Substitution
  , bisubstBiscopeR
  , substBiscopeR
    -- ** Abstraction
  , absBiscopeR
  , abs1BiscopeR
    -- ** Instantiation
  , instBiscopeR
  , inst1BiscopeR
    -- * @Biscope2@
  , Biscope2(..)
  , toBiscope2
  , fromBiscope2
    -- ** Substitution
  , bisubstBiscope2
    -- ** Abstraction
  , absBiscope2
  , abs1Biscope2
  , absScopeL
  , abs1ScopeL
    -- ** Instantiation
  , instBiscope2
  , inst1Biscope2
  , instBiscope2L
  , inst1Biscope2L
  , instBiscope2R
  , inst1Biscope2R
    -- * @Scope@
  , bisubstScope
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

newtype BiscopeL b f g a a' = BiscopeL { unBiscopeL :: g (Var b (f a)) a' }
deriveEq2 ''BiscopeL
deriveShow2 ''BiscopeL
deriveOrd2 ''BiscopeL

instance (Eq b, Eq1 f, Eq2 g, Eq a) => Eq1 (BiscopeL b f g a) where
  liftEq = liftEq2 (==)

instance (Eq b, Eq1 f, Eq2 g, Eq a, Eq a') => Eq (BiscopeL b f g a a') where
  (==) = eq1

instance (Show b, Show1 f, Show2 g, Show a) => Show1 (BiscopeL b f g a) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

instance (Show b, Show1 f, Show2 g, Show a, Show a') => Show (BiscopeL b f g a a') where
  showsPrec = showsPrec1

instance (Ord b, Ord1 f, Ord2 g, Ord a) => Ord1 (BiscopeL b f g a) where
  liftCompare = liftCompare2 compare

instance (Ord b, Ord1 f, Ord2 g, Ord a, Ord a') => Ord (BiscopeL b f g a a') where
  compare = compare

instance (forall x. Functor (g x)) => Functor (BiscopeL b f g a) where
  fmap f (BiscopeL s) = BiscopeL $ fmap f s

instance (forall x. Foldable (g x)) => Foldable (BiscopeL b f g a) where
  foldMap f (BiscopeL s) = foldMap f s

instance (forall x. Traversable (g x)) => Traversable (BiscopeL b f g a) where
  traverse f (BiscopeL s) = BiscopeL <$> traverse f s

instance (Functor f, Bifunctor g) => Bifunctor (BiscopeL b f g) where
  bimap f g (BiscopeL s) = BiscopeL $ bimap (fmap (fmap f)) g s

instance (Foldable f, Bifoldable g) => Bifoldable (BiscopeL b f g) where
  bifoldMap f g (BiscopeL s) = bifoldMap (foldMap (foldMap f)) g s

instance (Traversable f, Bitraversable g) => Bitraversable (BiscopeL b f g) where
  bitraverse f g (BiscopeL s) = BiscopeL <$> bitraverse (traverse (traverse f)) g s

instance (Bifunctor g, forall x. Monad (g x)) => Applicative (BiscopeL b f g a) where
  pure = return
  (<*>) = ap

instance (Bifunctor g, forall x. Monad (g x)) => Monad (BiscopeL b f g a) where
  return = BiscopeL . return
  (>>=) (BiscopeL s) f = BiscopeL (unBiscopeL . f =<< s)

instance (Bisubst g, f ~ Inner g) => Bisubst (BiscopeL b f g) where
  type Inner (BiscopeL b f g) = Inner g
  bireturn = BiscopeL . bireturn
  bisubst f g (BiscopeL s) =
    BiscopeL $
    bisubst
      (unvar (return . B) (fmap (F . return) . f =<<))
      (unBiscopeL . g)
      s

substBiscopeL ::
  (Bisubst g, f ~ Inner g) =>
  (tm -> g ty tm') ->
  BiscopeL b f g ty tm ->
  BiscopeL b f g ty tm'
substBiscopeL f =
  BiscopeL .
  bisubst return (bimap (F . return) id . f) .
  unBiscopeL

bisubstBiscopeL ::
  (Bisubst g, f ~ Inner g) =>
  (ty -> f ty') ->
  (tm -> g ty' tm') ->
  BiscopeL b f g ty tm ->
  BiscopeL b f g ty' tm'
bisubstBiscopeL f g =
  BiscopeL .
  bisubst
    (unvar (return . B) (fmap (F . return) . f =<<))
    (bimap (F . return) id . g) .
  unBiscopeL

absBiscopeL :: (Bisubst g, f ~ Inner g) => (a -> Maybe b) -> g a a' -> BiscopeL b f g a a'
absBiscopeL f =
  BiscopeL .
  bisubst
    (\a -> maybe (return . F $ return a) (return . B) $ f a)
    bireturn

abs1BiscopeL :: (Eq a, Bisubst g, f ~ Inner g) => a -> g a a' -> BiscopeL () f g a a'
abs1BiscopeL a = absBiscopeL (\x -> if x == a then Just () else Nothing)

instBiscopeL :: (Bisubst g, f ~ Inner g) => (b -> f a) -> BiscopeL b f g a a' -> g a a'
instBiscopeL f (BiscopeL s) = bisubst (unvar f id) bireturn s

inst1BiscopeL :: (Bisubst g, f ~ Inner g) => f a -> BiscopeL () f g a a' -> g a a'
inst1BiscopeL a = instBiscopeL (const a)

toBiscopeL :: (Bisubst g, f ~ Inner g) => g (Var b a) a' -> BiscopeL b f g a a'
toBiscopeL = BiscopeL . bimap (fmap return) id

fromBiscopeL :: (Bisubst g, f ~ Inner g) => BiscopeL b f g a a' -> g (Var b a) a'
fromBiscopeL = bisubst (unvar (return . B) (fmap F)) bireturn . unBiscopeL

newtype BiscopeR b (f :: * -> *) g a a'
  = BiscopeR { unBiscopeR :: g a (Var b (g a a')) }
deriveEq2 ''BiscopeR
deriveShow2 ''BiscopeR
deriveOrd2 ''BiscopeR

instance (Eq b, Eq1 f, Eq2 g, Eq a) => Eq1 (BiscopeR b f g a) where
  liftEq = liftEq2 (==)

instance (Eq b, Eq1 f, Eq2 g, Eq a, Eq a') => Eq (BiscopeR b f g a a') where
  (==) = eq1

instance (Show b, Show1 f, Show2 g, Show a) => Show1 (BiscopeR b f g a) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

instance (Show b, Show1 f, Show2 g, Show a, Show a') => Show (BiscopeR b f g a a') where
  showsPrec = showsPrec1

instance (Ord b, Ord1 f, Ord2 g, Ord a) => Ord1 (BiscopeR b f g a) where
  liftCompare = liftCompare2 compare

instance (Ord b, Ord1 f, Ord2 g, Ord a, Ord a') => Ord (BiscopeR b f g a a') where
  compare = compare

instance (forall x. Functor (g x)) => Functor (BiscopeR b f g a) where
  fmap f (BiscopeR s) = BiscopeR $ fmap (fmap (fmap f)) s

instance (forall x. Foldable (g x)) => Foldable (BiscopeR b f g a) where
  foldMap f (BiscopeR s) = foldMap (foldMap (foldMap f)) s

instance (forall x. Traversable (g x)) => Traversable (BiscopeR b f g a) where
  traverse f (BiscopeR s) = BiscopeR <$> traverse (traverse (traverse f)) s

instance (Functor f, Bifunctor g) => Bifunctor (BiscopeR b f g) where
  bimap f g (BiscopeR s) = BiscopeR $ bimap f (fmap (bimap f g)) s

instance (Foldable f, Bifoldable g) => Bifoldable (BiscopeR b f g) where
  bifoldMap f g (BiscopeR s) = bifoldMap f (foldMap (bifoldMap f g)) s

instance (Traversable f, Bitraversable g) => Bitraversable (BiscopeR b f g) where
  bitraverse f g (BiscopeR s) = BiscopeR <$> bitraverse f (traverse (bitraverse f g)) s

instance (Bifunctor g, forall x. Monad (g x)) => Applicative (BiscopeR b f g a) where
  pure = return
  (<*>) = ap

instance (Bifunctor g, forall x. Monad (g x)) => Monad (BiscopeR b f g a) where
  return = BiscopeR . return . F . return
  (>>=) (BiscopeR s) f = BiscopeR $ s >>= unvar (return . B) (>>= unBiscopeR . f)

instance (Bisubst g, f ~ Inner g) => Bisubst (BiscopeR b f g) where
  type Inner (BiscopeR b f g) = Inner g
  bireturn = BiscopeR . bireturn . F . bireturn
  bisubst f g (BiscopeR s) =
    BiscopeR $
    bisubst
      f
      (unvar (bireturn . B) (bisubst f (unBiscopeR . g)))
      s

substBiscopeR ::
  (Bisubst g, f ~ Inner g) =>
  (tm -> g ty tm') ->
  BiscopeR b f g ty tm ->
  BiscopeR b f g ty tm'
substBiscopeR f =
  BiscopeR .
  bisubst
    return
    (unvar
       (bireturn . B)
       (bisubst return (bimap id (F . bireturn) . f))) .
  unBiscopeR

bisubstBiscopeR ::
  (Bisubst g, f ~ Inner g) =>
  (ty -> f ty') ->
  (tm -> g ty' tm') ->
  BiscopeR b f g ty tm ->
  BiscopeR b f g ty' tm'
bisubstBiscopeR f g =
  BiscopeR .
  bisubst
    f
    (unvar
       (bireturn . B)
       (bisubst f (bimap id (F . bireturn) . g))) .
  unBiscopeR

absBiscopeR :: (Bisubst g, f ~ Inner g) => (a' -> Maybe b) -> g a a' -> BiscopeR b f g a a'
absBiscopeR f =
  BiscopeR .
  bisubst pure (\x -> maybe (bireturn . F $ bireturn x) (bireturn . B) $ f x)

abs1BiscopeR :: (Eq a', Bisubst g, f ~ Inner g) => a' -> g a a' -> BiscopeR () f g a a'
abs1BiscopeR a = absBiscopeR (\x -> if x == a then Just () else Nothing)

instBiscopeR :: (Bisubst g, f ~ Inner g) => (b -> g a a') -> BiscopeR b f g a a' -> g a a'
instBiscopeR f (BiscopeR s) = bisubst return (unvar f id) s

inst1BiscopeR :: (Bisubst g, f ~ Inner g) => g a a' -> BiscopeR () f g a a' -> g a a'
inst1BiscopeR a = instBiscopeR (const a)

toBiscopeR :: (Bisubst g, f ~ Inner g) => g a (Var b a') -> BiscopeR b f g a a'
toBiscopeR = BiscopeR . bimap id (fmap bireturn)

fromBiscopeR :: (Bisubst g, f ~ Inner g) => BiscopeR b f g a a' -> g a (Var b a')
fromBiscopeR = bisubst pure (unvar (bireturn . B) (bimap id F)) . unBiscopeR

bisubstScope ::
  (Bisubst g, f ~ Inner g) =>
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

instance (Eq b, Eq b', Eq1 f, Eq2 g, Eq a) => Eq1 (Biscope2 b b' f g a) where
  liftEq = liftEq2 (==)

instance (Eq b, Eq b', Eq1 f, Eq2 g, Eq a, Eq a') => Eq (Biscope2 b b' f g a a') where
  (==) = eq1

instance (Show b, Show b', Show1 f, Show2 g, Show a) => Show1 (Biscope2 b b' f g a) where
  liftShowsPrec = liftShowsPrec2 showsPrec showList

instance (Show b, Show b', Show1 f, Show2 g, Show a, Show a') => Show (Biscope2 b b' f g a a') where
  showsPrec = showsPrec1

instance (Ord b, Ord b', Ord1 f, Ord2 g, Ord a) => Ord1 (Biscope2 b b' f g a) where
  liftCompare = liftCompare2 compare

instance (Ord b, Ord b', Ord1 f, Ord2 g, Ord a, Ord a') => Ord (Biscope2 b b' f g a a') where
  compare = compare

instance (forall x. Functor (g x)) => Functor (Biscope2 b b' f g a) where
  fmap f (Biscope2 s) = Biscope2 $ fmap (fmap (fmap f)) s

instance (forall x. Foldable (g x)) => Foldable (Biscope2 b b' f g a) where
  foldMap f (Biscope2 s) = foldMap (foldMap (foldMap f)) s

instance (forall x. Traversable (g x)) => Traversable (Biscope2 b b' f g a) where
  traverse f (Biscope2 s) = Biscope2 <$> traverse (traverse (traverse f)) s

instance (Functor f, Bifunctor g) => Bifunctor (Biscope2 b b' f g) where
  bimap f g (Biscope2 s) =
    Biscope2 $ bimap (fmap (fmap f)) (fmap (bimap (fmap (fmap f)) g)) s

instance (Foldable f, Bifoldable g) => Bifoldable (Biscope2 b b' f g) where
  bifoldMap f g (Biscope2 s) =
    bifoldMap (foldMap (foldMap f)) (foldMap (bifoldMap (foldMap (foldMap f)) g)) s

instance (Traversable f, Bitraversable g) => Bitraversable (Biscope2 b b' f g) where
  bitraverse f g (Biscope2 s) =
    Biscope2 <$>
    bitraverse
      (traverse (traverse f))
      (traverse (bitraverse (traverse (traverse f)) g))
      s

instance (Bifunctor g, forall x. Monad (g x)) => Applicative (Biscope2 b b' f g a) where
  pure = return
  (<*>) = ap

instance (Bifunctor g, forall x. Monad (g x)) => Monad (Biscope2 b b' f g a) where
  return = Biscope2 . return . F . return
  (>>=) (Biscope2 s) f =
    Biscope2 $
    s >>= unvar (pure . B) (unBiscope2 . f =<<)

instance (Bisubst g, f ~ Inner g) => Bisubst (Biscope2 b b' f g) where
  type Inner (Biscope2 b b' f g) = Inner g
  bireturn = Biscope2 . bireturn . F . bireturn
  bisubst f g =
    Biscope2 .
    bisubst
      (unvar (pure . B) (fmap (F . pure) . f =<<))
      (unvar
         (bireturn . B)
         (bisubst
            (unvar (pure . B) (fmap (F . pure) . f =<<))
            (unBiscope2 . g))) .
    unBiscope2

toBiscope2 ::
  (Bisubst g, f ~ Inner g) =>
  g (Var b a) (Var b' a') ->
  Biscope2 b b' f g a a'
toBiscope2 = Biscope2 . bimap (fmap return) (fmap bireturn)

fromBiscope2 ::
  (Bisubst g, f ~ Inner g) =>
  Biscope2 b b' f g a a' ->
  g (Var b a) (Var b' a')
fromBiscope2 =
  bisubst
    unwrap
    (unvar (bireturn . B) (bisubst unwrap (bireturn . F))) .
    unBiscope2
  where
    unwrap = unvar (return . B) (fmap F)

absBiscope2 ::
  (Bisubst g, f ~ Inner g) =>
  (a -> Maybe b) ->
  (a' -> Maybe b') ->
  g a a' ->
  Biscope2 b b' f g a a'
absBiscope2 f g =
  Biscope2 .
  bisubst
    (\x -> pure . maybe (F $ pure x) B $ f x)
    (\x -> bireturn . maybe (F $ bireturn x) B $ g x)

abs1Biscope2 ::
  (Eq a, Eq a', Bisubst g, f ~ Inner g) =>
  a ->
  a' ->
  g a a' ->
  Biscope2 () () f g a a'
abs1Biscope2 a a' =
  absBiscope2
    (\x -> if a == x then Just () else Nothing)
    (\x -> if a' == x then Just () else Nothing)

absScopeL ::
  (Bisubst g, f ~ Inner g) =>
  (a -> Maybe b) ->
  Scope b' (g a) a' ->
  Biscope2 b b' f g a a'
absScopeL f =
  Biscope2 .
  bisubst
    (\x -> pure . maybe (F $ pure x) B $ f x)
    (unvar
       (bireturn . B)
       (bisubst
          (\x -> pure . maybe (F $ pure x) B $ f x)
          (bireturn . F . bireturn))) .
  unscope

abs1ScopeL ::
  (Eq a, Bisubst g, f ~ Inner g) =>
  a ->
  Scope b' (g a) a' ->
  Biscope2 () b' f g a a'
abs1ScopeL a = absScopeL (\x -> if x == a then Just () else Nothing)

instBiscope2 ::
  (Bisubst g, f ~ Inner g) =>
  (b -> f a) ->
  (b' -> g a a') ->
  Biscope2 b b' f g a a' -> g a a'
instBiscope2 f g =
  bisubst
    (unvar f id)
    (unvar g (bisubst (unvar f id) bireturn)) .
  unBiscope2

inst1Biscope2 :: (Bisubst g, f ~ Inner g) => f a -> g a a' -> Biscope2 () () f g a a' -> g a a'
inst1Biscope2 a b = instBiscope2 (const a) (const b)

instBiscope2L ::
  (Bisubst g, f ~ Inner g) =>
  (b -> f a) ->
  Biscope2 b b' f g a a' ->
  Scope b' (g a) a'
instBiscope2L f =
  Scope .
  bisubst
    (unvar f id)
    (unvar (bireturn . B) (bisubst (unvar f id) (bireturn . F . bireturn))) .
  unBiscope2

inst1Biscope2L ::
  (Bisubst g, f ~ Inner g) =>
  f a ->
  Biscope2 () b' f g a a' ->
  Scope b' (g a) a'
inst1Biscope2L a = instBiscope2L (const a)

instBiscope2R ::
  (Bisubst g, f ~ Inner g) =>
  (b' -> g a a') ->
  Biscope2 b b' f g a a' ->
  BiscopeL b f g a a'
instBiscope2R f =
  BiscopeL .
  bisubst
    pure
    (unvar (bimap (F . pure) id . f) id) .
  unBiscope2

inst1Biscope2R ::
  (Bisubst g, f ~ Inner g) =>
  g a a' ->
  Biscope2 b () f g a a' ->
  BiscopeL b f g a a'
inst1Biscope2R a = instBiscope2R (const a)

bisubstBiscope2 ::
  (Bisubst g, f ~ Inner g) =>
  (ty -> f ty') ->
  (tm -> g ty' tm') ->
  Biscope2 b b' f g ty tm ->
  Biscope2 b b' f g ty' tm'
bisubstBiscope2 f g =
  Biscope2 .
  bisubst
    (unvar (pure . B) (fmap (F . pure) . f =<<))
    (unvar
       (bireturn . B)
       (bisubst
          (unvar (pure . B) (fmap (F . pure) . f =<<))
          (bimap (F . pure) (F . bireturn) . g))) .
  unBiscope2
