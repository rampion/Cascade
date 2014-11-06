{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
module Cascade where
import Control.Category
import Control.Comonad
import Control.Monad.Identity
import Data.Char (toUpper)
import Prelude hiding (id, (.))
import System.Environment (getEnv, setEnv, getProgName)

-- generalized chain of invocations
data Cascade (w :: * -> *) (m :: * -> *) (ts :: [*]) where
  (:>>>)  :: (w a -> m b) -> Cascade w m (b ': ts) -> Cascade w m (a ': b ': ts)
  Done    :: Cascade w m '[t]
infixr 1 :>>>

-- compress into a function
cascade :: forall w m a b ts.
            (forall x y z. (w x -> m y) -> (w y -> m z) -> w x -> m z) ->
            Cascade w m (a ': b ': ts) -> w a -> m (Last (b ': ts))
cascade (>>>) (f :>>> fs) = case fs of
  Done      -> f
  _ :>>> _  -> f >>> cascade (>>>) fs


-- specialize to functions
type Cascade'   = Cascade Identity Identity
(>>>:) :: (a -> b) -> Cascade' (b ': ts) -> Cascade' (a ': b ': ts)
(>>>:) f c = fmap f :>>> c
infixr 1 >>>:

cascade' :: Cascade' (a ': b ': ts) -> a -> Last (a ': b ': ts)
cascade' fs = runIdentity . cascade (>>>) fs . Identity

-- specialize to monads
type CascadeM m = Cascade Identity m
(>=>:) :: (a -> m b) -> CascadeM m (b ': ts) -> CascadeM m (a ': b ': ts)
(>=>:) f c = (f . runIdentity) :>>> c
infixr 1 >=>:

cascadeM :: Monad m => CascadeM m (a ': b ': ts) -> a -> m (Last (a ': b ': ts))
cascadeM fs = cascade (\f g -> f >=> g . Identity) fs . Identity

-- specialize to comonads
type CascadeW w = Cascade w Identity
(=>=:) :: (w a -> b) -> CascadeW w (b ': ts) -> CascadeW w (a ': b ': ts)
(=>=:) f c = (Identity . f) :>>> c
infixr 1 =>=:

cascadeW :: Comonad w => CascadeW w (a ': b ': ts) -> w a -> Last (a ': b ': ts)
cascadeW fs = runIdentity . cascade (\f g -> runIdentity . f =>= g) fs

-- generalized sum
data AllOf (m :: * -> *) (ts :: [*]) where
  None :: AllOf m '[]
  (:&) :: a -> m (AllOf m ts) -> AllOf m (a ': ts)
type AllOf' = AllOf Identity

-- generalized product
data OneOf (w :: * -> *) (ts :: [*]) where
  Goose :: w a -> OneOf w (a ': as)
  Duck  :: OneOf w as -> OneOf w (a ': as)
type OneOf' = OneOf Identity

resume :: Cascade w m ts -> Cascade w m (Map (OneOf w) (Init (Tails ts)))
resume = undefined

record :: Cascade w m ts -> Cascade w m (Map (AllOf m) (Tail (Inits ts)))
record = undefined

recordr :: Cascade w m ts -> Cascade w m (Map AllOf' (Tail (RInits ts)))
recordr = undefined

-- examples
fc, gc :: Cascade' '[String, Int, Double, Double]
fc =  read          >>>:
      fromIntegral  >>>:
      (1/)          >>>: Done
gc =  length        >>>:
      (2^)          >>>:
      negate        >>>: Done

mc, nc :: CascadeM IO '[ String, (), String, String, () ]
mc =  putStrLn                >=>:
      const getLine           >=>:
      return . map toUpper    >=>:
      putStrLn                >=>: Done
nc =  print . length          >=>:
      const getProgName       >=>:
      getEnv                  >=>:
      setEnv "foo"            >=>: Done

wc, vc :: CascadeW ((,) Char) '[ Int, Char, Int, String ]
wc =  fst                       =>=:
      fromEnum . snd            =>=:
      uncurry (flip replicate)  =>=: Done
vc =  toEnum . snd              =>=:
      const 5                   =>=:
      show                      =>=: Done

-- alternate using functions from one cascade then the other
zigzag :: Cascade w m ts -> Cascade w m ts -> Cascade w m ts
zigzag Done Done = Done
zigzag (f :>>> fc) (_ :>>> gc) = f :>>> zigzag gc fc

-- type level list functions --

type family Head (as :: [a]) :: a where
  Head (a ': as) = a
type family Tail (as :: [a]) :: [a] where
  Tail (a ': as) = as
type family Tails (as :: [a]) :: [[a]] where
  Tails '[] = '[ '[] ]
  Tails (a ': as) = (a ': as) ': Tails as

type family Last (ts :: [a]) :: a where
  Last '[a] = a
  Last (a ': as) = Last as
type family Init (as :: [a]) :: [a] where
  Init '[a] = '[]
  Init (a ': as)  = a ': Init as
type family Inits (as :: [a]) :: [[a]] where
  Inits '[] = '[ '[] ]
  Inits (a ': as)  = '[] ': MapCons a (Inits as)

type family RInits_r (xss :: [[a]]) (xs :: [a]) :: [[a]] where
  RInits_r xss '[] = xss
  RInits_r xss (a ': as) = RInits_r (MapCons a xss) as
type RInits = RInits_r '[ '[] ]

type family MapCons (x :: a) (xss :: [[a]]) :: [[a]] where
  MapCons x '[] = '[]
  MapCons x (xs ': xss) = (x ': xs) ': MapCons x xss

type family Map (f :: a -> b) (as :: [a]) where
  Map f '[] = '[]
  Map f (a ': as) = f a ': Map f as
