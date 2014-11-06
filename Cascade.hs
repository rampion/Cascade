{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
module CascadeC where
import Control.Arrow
import Control.Category
import Control.Comonad
import Control.Monad.Identity
import Data.Char (toUpper)
import Prelude hiding (id, (.))
import System.Environment (getEnv, setEnv, getProgName)
import Data.Traversable
import Control.Applicative

-- reified categorical composition
data CascadeC (c :: * -> * -> *) (ts :: [*]) where
  (:>>>)  :: c x y -> CascadeC c (y ': zs) -> CascadeC c (x ': y ': zs)
  Done    :: CascadeC c '[t]
infixr 1 :>>>

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

-- specialize to comonads
type CascadeW w = CascadeC (Cokleisli w)
(=>=:) :: (w x -> y) -> CascadeW w (y ': zs) -> CascadeW w (x ': y ': zs)
(=>=:) f cw = Cokleisli f :>>> cw
infixr 1 =>=:

cascadeW :: Comonad w => CascadeW w (t ': ts) -> w t -> Last (t ': ts)
cascadeW = runCokleisli . cascade

-- monadic product
data AllOf (m :: * -> *) (ts :: [*]) where
  None :: AllOf m '[]
  (:&) :: a -> m (AllOf m ts) -> AllOf m (a ': ts)
type AllOf' = AllOf Identity

-- comonadic sum
data OneOf (w :: * -> *) (ts :: [*]) where
  Here  :: w a -> OneOf w (a ': as)
  There :: OneOf w as -> OneOf w (a ': as)
type OneOf' = OneOf Identity

class Functionish c where
  type Src c :: * -> *
  type Dst c :: * -> *
  run   :: c a b -> Src c a -> Dst c b
  wrap  :: (Src c a -> Dst c b) -> c a b

instance Functionish (->) where
  type Src (->) = Identity
  type Dst (->) = Identity
  run  c = fmap c
  wrap f = runIdentity . f . Identity

instance Functionish (Kleisli m) where
  type Src (Kleisli m) = Identity
  type Dst (Kleisli m) = m
  run c   = runKleisli c . runIdentity
  wrap f  = Kleisli $ f . Identity

instance Functionish (Cokleisli w) where
  type Src (Cokleisli w) = w
  type Dst (Cokleisli w) = Identity
  run c   = Identity . runCokleisli c
  wrap f  = Cokleisli $ runIdentity . f

type family OneOfNonEmptyTails (w :: * -> *) (ts :: [*]) :: [*] where
  OneOfNonEmptyTails w '[] = '[]
  OneOfNonEmptyTails w (a ': as) = OneOf w (a ': as) ': OneOfNonEmptyTails w as

resume :: (Functionish c, w ~ Src c, m ~ Dst c, Comonad w, Monad m, Traversable w, Applicative m) => 
          CascadeC c ts -> CascadeM m (OneOfNonEmptyTails w ts)
resume Done = Done
resume (f :>>> fs) = oneOf (run f) >=>: resume fs

oneOf :: (Comonad w, Monad m, Traversable w, Applicative m) =>
          (w x -> m y) -> OneOf w (x ': y ': zs) -> m (OneOf w (y ': zs))
oneOf _ (There oo) = return oo
oneOf f (Here wx)  = liftM Here . sequenceA $ wx =>> f

{-
record :: CascadeC c ts -> CascadeC c (Map (AllOf m) (Tail (Inits ts)))
record = undefined

recordr :: CascadeC c ts -> CascadeC c (Map AllOf' (Tail (RInits ts)))
recordr = undefined
-}

-- examples
fc, gc :: Cascade '[String, Int, Double, Double]
fc =  read          :>>>
      fromIntegral  :>>>
      (1/)          :>>> Done
gc =  length        :>>>
      (2^)          :>>>
      negate        :>>> Done

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
zigzag :: CascadeC c ts -> CascadeC c ts -> CascadeC c ts
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

type RInits as  = Reverse (Map Reverse (Tails as))
type Inits as   = RInits (Reverse as)

type family ReverseR (rs :: [a]) (as :: [a]) :: [a] where
  ReverseR rs '[] = rs
  -- ReverseR rs (a ': as) = ReverseR (a ': rs) as
type Reverse = ReverseR '[]

type family Map (f :: a -> b) (as :: [a]) where
  Map f '[] = '[]
  Map f (a ': as) = f a ': Map f as
