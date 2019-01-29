{-# language MultiParamTypeClasses, FunctionalDependencies #-}
module Bisubst.Class where

import Data.Bifunctor

-- |
-- @bibind return bireturn = id@
--
-- @bijoin . bimap return bireturn = id@
class (Bifunctor g, Monad f) => Bisubst g f | g -> f where
  {-# minimal (bisubst | bijoin), bireturn #-}
  bireturn :: a' -> g a a'

  bisubst :: (a -> f b) -> (a' -> g b b') -> g a a' -> g b b'
  bisubst f g = bijoin . bimap f g

  bijoin :: g (f a) (g a a') -> g a a'
  bijoin = bisubst id id

bisubstBimapDefault :: Bisubst g f => (a -> c) -> (b -> d) -> g a b -> g c d
bisubstBimapDefault f g = bisubst (pure . f) (bireturn . g)