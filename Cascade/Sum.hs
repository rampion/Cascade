{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE RankNTypes             #-}
module Cascade.Sum where
import Cascade
import Cascade.Util.ListKind

import Control.Arrow (Kleisli(..))
import Control.Comonad (Cokleisli(..), Comonad(..), liftW, (=>>))
import Control.Monad (liftM)
import Control.Monad.Identity (Identity(..))

-- Comonadic sum
--
-- Mostly equivalent to 
--
--    type family SumW w ts where
--      SumW w (a ': as) = Either (w a) (SumW w as)
--      SumW w '[]       = Void
--
-- Made concrete to avoid injective type errors
data SumW (w :: * -> *) (ts :: [*]) where
  Here  :: w a -> SumW w (a ': as)
  There :: SumW w as -> SumW w (a ': as)

-- specialize for the identity comonad, since that'll be common
type Sum = SumW Identity

here :: a -> Sum (a ': as)
here = Here . Identity

there :: Sum as -> Sum (a ': as)
there = There

instance Show (SumW Identity '[]) where
  showsPrec _ _ = error "impossible value of type Sum '[]"

-- show as "here x", "there.here $ x", "there.there.there.here $ x" to avoid lisping
instance (Show a, Show (SumW Identity as)) => Show (SumW Identity (a ': as)) where
  showsPrec (-1) (Here (Identity a))  = showString "here $ " . showsPrec 0 a
  showsPrec (-1) (There as)           = showString "there." . showsPrec (-1) as
  showsPrec p (Here (Identity a))     = showParen (p > 10) $ showString "here " . showsPrec 11 a
  showsPrec p (There as)              = showParen (p > 10) $ showString "there." . showsPrec (-1) as

-- This could be more simply expressed as
--
--     type TailSumsW w ts = Map (SumW w) (Init (Tails ts))
--
-- however, GHC can't quite figure out the equivalences we need
--
--     Could not deduce (Map (SumW w) (Init ((y : zs) : Tails zs)) ~ (SumW w (y : zs) : zs0))
--
-- XXX: This type family is actually more restrictive than we need - we should
-- actually use  `SumW w (a ': Concat as bs)`, as we can pass through any b
-- values untouched. Haven't gotten that to work yet though.
type family TailSumsW (w :: * -> *) (ts :: [*]) :: [*] where
  TailSumsW w '[] = '[]
  TailSumsW w (a ': as) = SumW w (a ': as) ': TailSumsW w as
type TailSums ts = TailSumsW Identity ts

-- lift a kleisli arrow into an arrow on the first element of a sum (if given)
-- (similar to \f -> either f id)
pops :: Monad m
     => (w x -> m (w y))
     -> SumW w (x ': y ': zs) -> m (SumW w (y ': zs))
pops _ (There oo) = return oo
pops f (Here wx)  = liftM Here $ f wx

-- transform a categorical cascade into a monadic cascade, resumable from any
-- point in the computation (by passing the proper sum value as input)
resumeC :: Monad m
        => (forall a b. c a b -> w a -> m (w b))
        -> CascadeC c ts 
        -> CascadeM m (TailSumsW w ts)
resumeC over Done = Done
resumeC over (f :>>> fs) = pops (over f) >=>: resumeC over fs

-- specialize to monadic cascades
resumeM :: Monad m => CascadeM m ts -> CascadeM m (TailSums ts)
resumeM = resumeC $ \c -> liftM Identity . runKleisli c . runIdentity

-- specialize to comonadic cascades
resumeW :: Comonad w => CascadeW w ts -> Cascade (TailSumsW w ts)
resumeW = unwrapM . resumeC (\c -> Identity . (=>> runCokleisli c))

-- specialize to functional cascades
resume :: Cascade ts -> Cascade (TailSums ts)
resume  = unwrapM . resumeC (\c -> fmap (Identity . c))
