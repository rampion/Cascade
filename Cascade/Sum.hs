{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE RankNTypes             #-}
module Cascade.Sum where
import Cascade

import Control.Arrow (Kleisli(..))
import Control.Comonad (Cokleisli(..), Comonad(..), liftW, (=>>))
import Control.Monad (liftM)
import Control.Monad.Identity (Identity(..))

-- comonadic sum
data SumW (w :: * -> *) (ts :: [*]) where
  Here  :: w a -> SumW w (a ': as)
  There :: SumW w as -> SumW w (a ': as)
type Sum = SumW Identity

here :: a -> Sum (a ': as)
here = Here . Identity

there :: Sum as -> Sum (a ': as)
there = There

instance Show (SumW Identity '[]) where
  showsPrec _ _ = error "impossible value of type Sum '[]"

instance (Show a, Show (SumW Identity as)) => Show (SumW Identity (a ': as)) where
  showsPrec (-1) (Here (Identity a))  = showString "here $ " . showsPrec 0 a
  showsPrec (-1) (There as)           = showString "there." . showsPrec (-1) as
  showsPrec p (Here (Identity a))     = showParen (p > 10) $ showString "here " . showsPrec 11 a
  showsPrec p (There as)              = showParen (p > 10) $ showString "there." . showsPrec (-1) as

type family TailSumsW (w :: * -> *) (ts :: [*]) :: [*] where
  TailSumsW w '[] = '[]
  TailSumsW w (a ': as) = SumW w (a ': as) ': TailSumsW w as
type TailSums ts = TailSumsW Identity ts

resumeC :: (Comonad w, Monad m) => 
            (forall x. w (m x) -> m (w x)) -> 
            (forall a b. c a b -> w a -> m b) -> 
            CascadeC c ts -> CascadeM m (TailSumsW w ts)
resumeC _ _ Done = Done
resumeC swap run (f :>>> fs) = pops swap (run f) >=>: resumeC swap run fs

resumeM :: Monad m => CascadeM m ts -> CascadeM m (TailSums ts)
resumeM = resumeC (liftM Identity . runIdentity) (\c -> runKleisli c . runIdentity)

resumeW :: Comonad w => CascadeW w ts -> Cascade (TailSumsW w ts)
resumeW = unwrapM . resumeC (Identity . liftW runIdentity) (\c -> Identity . runCokleisli c)

resume :: Cascade ts -> Cascade (TailSums ts)
resume = unwrapM . resumeC id fmap

pops :: (Comonad w, Monad m) =>
          (forall t. w (m t) -> m (w t)) -> (w x -> m y) -> 
          SumW w (x ': y ': zs) -> m (SumW w (y ': zs))
pops _ _ (There oo) = return oo
pops swap f (Here wx)  = liftM Here . swap $ wx =>> f
