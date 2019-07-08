{-# language AllowAmbiguousTypes #-}
{-# language FlexibleContexts #-}
{-# language TypeFamilies #-}
module Bisubst.Class where

import Data.Bifunctor

-- |
-- @bibind return bireturn = id@
--
-- @bijoin . bimap return bireturn = id@
class (Bifunctor g, Monad (Inner g)) => Bisubst g where
  type Inner g :: * -> *
  {-# minimal (bisubst | bijoin), bireturn #-}
  bireturn :: a' -> g a a'

  bisubst :: (a -> Inner g b) -> (a' -> g b b') -> g a a' -> g b b'
  bisubst f g = bijoin . bimap f g

  bijoin :: g (Inner g a) (g a a') -> g a a'
  bijoin = bisubst id id

bisubstBimapDefault :: Bisubst g => (a -> c) -> (b -> d) -> g a b -> g c d
bisubstBimapDefault f g = bisubst (pure . f) (bireturn . g)
