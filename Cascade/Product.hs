{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE UndecidableInstances   #-} -- for RInits
module Cascade.Product where
import Cascade
import Cascade.Util.ListKind

import Control.Arrow (Kleisli(..))
import Control.Comonad (Cokleisli(..), Comonad(..), liftW, (=>>))
import Control.Monad (liftM)
import Control.Monad.Identity (Identity(..))

-- Monadic product
-- 
-- Mostly equivalent to 
--
--    type family ProductM w ts where
--      ProductM m (a ': as) = (a, m (ProductM m as))
--      ProductM m '[]       = ()
--
-- Made concrete to avoid injective type errors
data ProductM (m :: * -> *) (ts :: [*]) where
  None :: ProductM m '[]
  (:*) :: a -> m (ProductM m ts) -> ProductM m (a ': ts)
infixr 5 :*

-- specialize for the Identity monad, since that'll be common
type Product = ProductM Identity
(*:) :: a -> Product ts -> Product (a ': ts)
a *: as = a :* return as
infixr 5 *:

instance Show (ProductM Identity '[]) where
  showsPrec _ None = showString "None"

instance (Show a, Show (ProductM Identity as)) => Show (ProductM Identity (a ': as)) where
  showsPrec p (a :* (Identity as)) = showParen (p > 10) $ showsPrec 5 a . showString " *: " . showsPrec 5 as

-- Now, ideally, I'd like to be able to lift a `CascadeC c ts` into a chain of
-- transformations between longer and longer `ProductM`s, so when you ultimately
-- ran the cascade, you could generate as much of the intermediate results as
-- you wanted.
--
-- I think this would require something like
--
--    replayC0 :: CascadeWM w m '[a] -> CascadeW w '[ ProductM m '[a] ]
--    replayC0 Done = Done
--    
--    replayC1 :: CascadeWM w m '[a,b] -> CascadeW w '[ ProductM m '[a], ProductM m '[a,b] ]
--    replayC1 (f :>>> Done) = unshifts f :>>> Done
--    
--    replayC2 :: CascadeWM w m '[a,b] 
--             -> CascadeW w '[ ProductM m '[a], ProductM m '[a,b], ProductM m '[a, b, c] ]
--    replayC2 (f :>>> g :>>> Done) = unshifts f :>>> unshifts g :>>> Done
--
--    ...
--
--    replayC :: CascadeWM w m ts -> CascadeW w (Map (ProductM m) (Tail (Inits ts)))
--    replayC Done = Done
--    replayC (f :>>> fs) = unshifts f :>>> replayC fs
--
-- where `unshifts` has the given arrow simply append its result to the end of
-- the product
--
--    unshifts :: (w (Last as) -> m b) -> w (ProductM m as) -> ProductM m (Snoc b as)
--
-- But I haven't gotten this to quite work yet.
--
-- For one thing, you actually want `replayC` to be polymorphic in the `init` of
-- the type list. You don't care how long the ProductM is you get - you're just
-- skipping to the end.
--
-- In any case, I suspect this is likely to be slower than normally desired
-- since you have to step all the way through to the end of the `ProductM` each
-- time. Fortunately, the reversed `ProductM Identity` solution is easier and
-- faster


-- Given ts = [a,b..z], for any ts' this generates the list of `Product`s
--
--  [ Product (a : ts'), Product (b : a : ts'), ..., Product (z : ... : b : a : ts') ]
--
-- Note that the elements of ts are reversed as they are prepended to ts', so
-- the most recently prepended type may be extracted from the front of the `Product`
--
type family RInitProducts (ts :: [*]) (ts' :: [*]) :: [*] where
  RInitProducts (a ': as) ts' = Product (a ': ts') ': RInitProducts as (a ': ts')
  RInitProducts '[] ts' = '[]

-- lift a cokleisli arrow into an arrow on the first element of a product
-- (similar to \f as@(a,_) -> (f a, as) )
pushes :: Comonad w
       => (w y -> x) 
       -> w (Product (y ': zs)) -> Product (x ': y ': zs)
pushes f wyzs = f wy *: yzs
  where wy = liftW (\(y :* _) -> y) wyzs
        yzs = extract wyzs

-- transform a comonadic cascade to cache the partial results seen along the way
recordW :: Comonad w
        => CascadeW w (t ': ts) -> CascadeW w (RInitProducts (t ': ts) ts')
recordW Done = Done
recordW (Cokleisli f :>>> fs) = pushes f =>=: recordW fs

-- specialize for functional cascades
record :: Cascade (t ': ts) -> Cascade (RInitProducts (t ': ts) ts')
record = unwrapW . recordW . wrapW
