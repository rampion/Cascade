{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE ConstraintKinds        #-}
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

type family Last (ts :: [a]) :: a where
  Last '[a] = a
  Last (a ': as) = Last as

-- compress into a function
cascade :: Category c => CascadeC c (t ': ts) -> c t (Last (t ': ts))
cascade Done = id
cascade (f :>>> fs) = f >>> cascade fs

-- ideally, convert this into a transformation between Cascades
-- replayM :: Monad m => CascadeM m (t ': ts) -> t -> ProductM m (t ': ts)
-- replayM Done t = t :* return None
-- replayM (Kleisli f :>>> fs) a = a :* liftM (replayM fs) (f a)

data DebuggerM (m :: * -> *) (past :: [*]) (current :: *) (future :: [*]) where

  Begin     :: (a -> m (DebuggerM m '[a] b cs))
            -> DebuggerM m '[] a (b ': cs)

  Break     :: (a -> m (DebuggerM m (a ': z ': ys) b cs)) 
            -> DebuggerM m ys z (a ': b ': cs)
            -> z
            -> a 
            -> DebuggerM m (z ': ys) a (b ': cs)

  End       :: DebuggerM m ys z '[a]
            -> z
            -> a
            -> DebuggerM m (z ': ys) a '[]

instance (All Show zs, All Show bs, Show a) => Show (DebuggerM m zs a bs) where
  showsPrec p d = case d of
      Begin _       -> showString "Begin" 
      Break _ _ z a -> showParen (p > 10) $ showString "Break" . showIO z a
      End     _ z a -> showParen (p > 10) $ showString "End  " . showIO z a
    where showIO z a =  showString " { given = ".  showsPrec 11 z . 
                        showString ", returned = " . showsPrec 11 a . 
                        showString " }"

type family All (c :: * -> Constraint) (xs :: [*]) :: Constraint where
  All c '[] = ()
  All c (a ': as) = (c a, All c as)

printHistory :: (All Show zs, All Show bs, Show a) => DebuggerM m zs a bs-> IO ()
printHistory d@(Begin _      ) = print d
printHistory d@(Break _ _ _ _) = print d >> printHistory (back d)
printHistory d@(End     _ _ _) = print d >> printHistory (back d)

rundmc :: IO (DebuggerM IO '[String, String, (), [Char]] () '[])
rundmc = debugM >>> use "walk this way" >=> step >=> step >=> step $ mc

given :: DebuggerM m (z ': ys) a bs -> z
given (Break _ _ z _) = z
given (End     _ z _) = z

returned :: DebuggerM m (z ': ys) a bs -> a
returned (Break _ _ _ a) = a
returned (End     _ _ a) = a

back :: DebuggerM m (z ': ys) a bs -> DebuggerM m ys z (a ': bs)
back (Break _ d _ _) = d
back (End     d _ _) = d

redo :: DebuggerM m (a ': z ': ys) b cs -> m (DebuggerM m (a ': z ': ys) b cs)
redo = step . back

redoWith :: a -> DebuggerM m (a ': zs) b cs -> m (DebuggerM m (a ': zs) b cs)
redoWith x = use x . back

use :: a -> DebuggerM m zs a (b ': cs) -> m (DebuggerM m (a ': zs) b cs)
use a (Begin f      ) = f a
use a (Break f _ _ _) = f a

step :: DebuggerM m (z ': ys) a (b ': cs) -> m (DebuggerM m (a ': z ': ys) b cs)
step (Break f _ _ a) = f a

debugM :: Monad m => CascadeM m (a ': b ': cs) -> DebuggerM m '[] a (b ': cs)
debugM (f :>>> fs) = fix $ \d ->  Begin (go f fs d)
  where go :: Monad m
           => Kleisli m a b
           -> CascadeM m (b ': cs)
           -> DebuggerM m zs a (b ': cs)
           -> (a -> m (DebuggerM m (a ': zs) b cs))
        go (Kleisli f) Done         d a = End d a `liftM` f a
        go (Kleisli f) (f' :>>> fs) d a = do
          b <- f a
          let d' = Break (go f' fs d') d a b
          return d'

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
data ProductM (m :: * -> *) (ts :: [*]) where
  None :: ProductM m '[]
  (:*) :: a -> m (ProductM m ts) -> ProductM m (a ': ts)
type Product = ProductM Identity
infixr 5 :*

(*:) :: a -> Product ts -> Product (a ': ts)
a *: as = a :* return as
infixr 5 *:

instance Show (ProductM Identity '[]) where
  showsPrec _ None = showString "None"

instance (Show a, Show (ProductM Identity as)) => Show (ProductM Identity (a ': as)) where
  showsPrec p (a :* (Identity as)) = showParen (p > 10) $ showsPrec 5 a . showString " *: " . showsPrec 5 as

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

transform :: (forall a b. c a b -> c' a b) -> CascadeC c ts -> CascadeC c' ts
transform _ Done = Done
transform g (f :>>> fs) = g f :>>> transform g fs

unwrapM :: CascadeC (Kleisli Identity) ts -> Cascade ts
unwrapM = transform $ \f -> runIdentity . runKleisli f

pops :: (Comonad w, Monad m) =>
          (forall t. w (m t) -> m (w t)) -> (w x -> m y) -> 
          SumW w (x ': y ': zs) -> m (SumW w (y ': zs))
pops _ _ (There oo) = return oo
pops swap f (Here wx)  = liftM Here . swap $ wx =>> f

pushes :: (y -> x) -> Product (y ': zs) -> Product (x ': y ': zs)
pushes f yzs@(y :* _) = f y *: yzs

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
