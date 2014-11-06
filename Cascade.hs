{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE UndecidableInstances   #-}
module Cascade where
import GHC.Prim         (Constraint)
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
infixr 5 :&

(&:) :: a -> AllOf' ts -> AllOf' (a ': ts)
a &: as = a :& return as
infixr 5 &:

instance Show (AllOf Identity '[]) where
  showsPrec _ None = showString "None"

instance (Show a, Show (AllOf Identity as)) => Show (AllOf Identity (a ': as)) where
  showsPrec p (a :& (Identity as)) = showParen (p > 10) $ showsPrec 5 a . showString " &: " . showsPrec 5 as

-- comonadic sum
data OneOf (w :: * -> *) (ts :: [*]) where
  Here  :: w a -> OneOf w (a ': as)
  There :: OneOf w as -> OneOf w (a ': as)
type OneOf' = OneOf Identity

here :: a -> OneOf' (a ': as)
here = Here . Identity

there :: OneOf' as -> OneOf' (a ': as)
there = There

instance Show (OneOf Identity '[]) where
  showsPrec _ _ = error "impossible value of type OneOf '[]"

instance (Show a, Show (OneOf Identity as)) => Show (OneOf Identity (a ': as)) where
  showsPrec (-1) (Here (Identity a))  = showString "here $ " . showsPrec 0 a
  showsPrec (-1) (There as)           = showString "there." . showsPrec (-1) as
  showsPrec p (Here (Identity a))     = showParen (p > 10) $ showString "here " . showsPrec 11 a
  showsPrec p (There as)              = showParen (p > 10) $ showString "there." . showsPrec (-1) as

class AsFunction c where
  type Src c :: * -> *
  type Dst c :: * -> *
  run   :: c a b -> Src c a -> Dst c b
  -- wrap  :: (Src c a -> Dst c b) -> c a b

instance AsFunction (->) where
  type Src (->) = Identity
  type Dst (->) = Identity
  run  c = fmap c
  -- wrap f = runIdentity . f . Identity

instance AsFunction (Kleisli m) where
  type Src (Kleisli m) = Identity
  type Dst (Kleisli m) = m
  run c   = runKleisli c . runIdentity
  -- wrap f  = Kleisli $ f . Identity

instance AsFunction (Cokleisli w) where
  type Src (Cokleisli w) = w
  type Dst (Cokleisli w) = Identity
  run c   = Identity . runCokleisli c
  -- wrap f  = Cokleisli $ runIdentity . f

{-
type family OneOfNonEmptyTails (w :: * -> *) (ts :: [*]) :: [*] where
  OneOfNonEmptyTails w '[] = '[]
  OneOfNonEmptyTails w (a ': as) = OneOf w (a ': as) ': OneOfNonEmptyTails w as

resume :: (AsFunction c, w ~ Src c, m ~ Dst c, Comonad w, Monad m, Traversable w, Applicative m) => 
          CascadeC c ts -> CascadeM m (OneOfNonEmptyTails w ts)
resume Done = Done
resume (f :>>> fs) = oneOf (run f) >=>: resume fs

oneOf :: (Comonad w, Monad m, Traversable w, Applicative m) =>
          (w x -> m y) -> OneOf w (x ': y ': zs) -> m (OneOf w (y ': zs))
oneOf _ (There oo) = return oo
oneOf f (Here wx)  = liftM Here . sequenceA $ wx =>> f
-}

-- simple cases
resume' :: CascadeW w ts -> Cascade (Map (OneOf w) (Init (Tails ts)))
resume' Done = Done
resume' (Cokleisli f :>>> fs) = undefined

record' :: CascadeM m ts -> Cascade (Map (AllOf m) (Tail (Inits ts)))
record' Done = Done
record' (Kleisli f :>>> fs) = undefined

recordr' :: Cascade ts -> Cascade (Map AllOf' (Tail (RInits ts)))
recordr' Done = Done
recordr' (f :>>> fs) = undefined
-- recordr' (f :>>> fs) = (\as@(a :& _) -> undefined) :>>> recordr' fs

{- 
-- complex cases
resume :: (AsFunction c, m ~ Dst c, w ~ Src c) => 
            CascadeC c ts -> CascadeM m (Map (OneOf w) (Init (Tails ts)))
record :: (AsFunction c, m ~ Dst c, w ~ Src c) => 
            CascadeC c ts -> CascadeW w (Map (AllOf m) (Tail (Inits ts)))
recordr :: (AsFunction c, m ~ Dst c, w ~ Src c) => 
            CascadeC c ts -> CascadeW w (Map (AllOf m) (Tail (RInits ts)))
-}

{-
type family AllOfNonEmptyInits (m :: * -> *) (ts :: [*]) :: [*] where
  AllOfNonEmptyInits m '[]        = '[]
  AllOfNonEmptyInits m (a ': as)  = AllOf m '[a] ': MapCons a (AllOfNonEmptyInits m as)

type family MapCons (a :: *) (ts :: [*]) :: [*] where
  MapCons a '[] = '[]
  MapCons a (AllOf m ts ': ms) = AllOf m (a ': ts) ': MapCons a ts


record :: (AsFunction c, w ~ Src c, m ~ Dst c) =>
            CascadeC c ts -> CascadeW w (AllOfNonEmptyInits m ts)
            -- CascadeC c ts -> CascadeW w (Map (AllOf m) (Tail (Inits ts)))
record Done = Done
-- record (f :>>> fs) = allOf (run f) =>=: record fs

sequenceAllOf :: (Monad m, Comonad w, Applicative m, Traversable w) => 
                  w (AllOf m ts) -> AllOf m (Map w ts)
sequenceAllOf wao = case extract wao of
    None      -> None
    a :& mas  -> liftW headAO wao :& liftM sequenceAllOf (sequenceA $ liftW tailAO wao)
  where headAO (a :& _) = a
        tailAO (_ :& mas) = mas


-}
{-
allOf :: (Init ts' ~ ts, Last (t ': ts) ~ x, Last (t ': ts') ~ y) => 
        (w x -> m y) -> w (AllOf m (t ': ts)) -> AllOf m (t ': ts')
allOf f wao

  f :: 

a :& mas = (a :&) $ do
  as <- mas
  case as of
    (_ :& _) -> allOf f as
    None -> undefined
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

type family RInits (as :: [a]) :: [[a]] where
  RInits '[] = '[ '[] ]
  RInits (a ': as) = '[] ': Map (Snoc a) (RInits as)

type family Inits (as :: [a]) :: [[a]] where
  Inits '[] = '[ '[] ]
  Inits (a ': as) = '[] ': Map (Cons a) (Inits as)

type family Snoc (t :: a) (ts :: [a]) :: [a] where
  Snoc a '[] = '[a]
  Snoc a (b ': cs) = b ': Snoc a cs

type family Cons (t :: a) (ts :: [a]) :: [a] where
  Cons a as = a ': as

type family Map (f :: a -> b) (as :: [a]) where
  Map f '[] = '[]
  Map f (a ': as) = f a ': Map f as
