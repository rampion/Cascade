{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
module Cascade where
import Cascade.Util.ListKind (Last)

import Control.Arrow (Kleisli(..))
import Control.Category (Category(..), (>>>))
import Control.Comonad (Cokleisli(..), Comonad(..))
import Control.Monad.Identity (Identity(..))
import Prelude hiding (id, (.))

-- reified categorical composition
data CascadeC (c :: t -> t -> *) (ts :: [t]) where
  (:>>>)  :: c x y -> CascadeC c (y ': zs) -> CascadeC c (x ': y ': zs)
  Done    :: CascadeC c '[t]
infixr 1 :>>>

-- transform the underlying category used in a cascade
transform :: (forall a b. c a b -> c' a b) -> CascadeC c ts -> CascadeC c' ts
transform _ Done = Done
transform g (f :>>> fs) = g f :>>> transform g fs

-- compress into a function
cascade :: Category c => CascadeC c (t ': ts) -> c t (Last (t ': ts))
cascade Done = id
cascade (f :>>> fs) = f >>> cascade fs

-- specialize to functions
type Cascade   = CascadeC (->)

-- specialize to monads
type CascadeM m = CascadeC (Kleisli m)
(>=>:) :: (x -> m y) -> CascadeM m (y ': zs) -> CascadeM m (x ': y ': zs)
(>=>:) f cm = Kleisli f :>>> cm
infixr 1 >=>:

cascadeM :: Monad m => CascadeM m (t ': ts) -> t -> m (Last (t ': ts))
cascadeM = runKleisli . cascade

-- transform a simple cascade to and from a Kleisli cascade
unwrapM :: CascadeM Identity ts -> Cascade ts
unwrapM = transform $ \f -> runIdentity . runKleisli f

wrapM :: Monad m => Cascade ts -> CascadeM m ts
wrapM = transform $ \f -> Kleisli $ return . f

-- specialize to comonads
type CascadeW w = CascadeC (Cokleisli w)
(=>=:) :: (w x -> y) -> CascadeW w (y ': zs) -> CascadeW w (x ': y ': zs)
(=>=:) f cw = Cokleisli f :>>> cw
infixr 1 =>=:

cascadeW :: Comonad w => CascadeW w (t ': ts) -> w t -> Last (t ': ts)
cascadeW = runCokleisli . cascade

-- transform a simple cascade to and from a Cokleisli cascade
unwrapW :: CascadeW Identity ts -> Cascade ts
unwrapW = transform $ \f -> runCokleisli f . Identity

wrapW :: Comonad w => Cascade ts -> CascadeW w ts
wrapW = transform $ \f -> Cokleisli $ f . extract
