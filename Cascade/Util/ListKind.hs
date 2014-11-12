{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE UndecidableInstances   #-} -- for RInits
module Cascade.Util.ListKind where
import GHC.Prim (Constraint)

-- type level version of all :: (a -> Bool) -> [a] -> Bool
type family All (c :: a -> Constraint) (xs :: [a]) :: Constraint where
  All c '[] = ()
  All c (a ': as) = (c a, All c as)

-- type level version of last :: [a] -> a
type family Last (ts :: [a]) :: a where
  Last '[a] = a
  Last (a ': as) = Last as

-- type level version of map :: (a -> b) -> [a] -> [b]
type family Map (f :: a -> b) (ts :: [a]) :: [b] where
  Map f '[] = '[]
  Map f (a ': as) = f a ': Map f as

-- type level version of tails :: [a] -> [[a]]
type family Tails (as :: [a]) :: [[a]] where
  Tails '[] = '[ '[] ]
  Tails (a ': as) = (a ': as) ': Tails as

-- type level version of tail :: [a] -> [a]
type family Tail (as :: [a]) :: [a] where
  Tail (a ': as) = as

-- type level version of init :: [a] -> [a]
type family Init (as :: [a]) :: [a] where
  Init '[a] = '[]
  Init (a ': as)  = a ': Init as

-- type level version of rinits :: [a] -> [[a]] ; rinits = reverse . inits . reverse
type family RInits (as :: [a]) :: [[a]] where
  RInits '[] = '[ '[] ]
  RInits (a ': as) = '[] ': Map (Snoc a) (RInits as)

-- type level version of snoc :: a -> [a] -> [a] ; snoc a = reverse . (a:) . reverse
type family Snoc (x :: a) (xs :: [a]) :: [a] where
  Snoc x '[] = '[x]
  Snoc x (a ': as) = a ': Snoc x as

-- type level version of zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
type family ZipWith (f :: a -> b -> c) (as :: [a]) (bs :: [b]) :: [c] where
  ZipWith f '[] '[] = '[]
  ZipWith f (a ': as) (b ': bs) = f a b ': ZipWith f as bs

type family Concat (as :: [a]) (bs :: [a]) :: [a] where
  Concat '[] bs = bs
  Concat (a ': as) bs = a ': Concat as bs
