{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
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
