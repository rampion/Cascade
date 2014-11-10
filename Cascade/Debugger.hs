{-# LANGUAGE ConstraintKinds        #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
module Cascade.Debugger where

import Control.Arrow
import Control.Category
import Prelude hiding (id, (.))
import GHC.Prim         (Constraint)

import Cascade

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

printHistory :: (All Show zs, All Show bs, Show a) => DebuggerM m zs a bs-> IO ()
printHistory d@(Begin _      ) = print d
printHistory d@(Break _ _ _ _) = print d >> printHistory (back d)
printHistory d@(End     _ _ _) = print d >> printHistory (back d)

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
debugM (f :>>> fs) = let d = Begin (go f fs d) in d
  where go :: Monad m
           => Kleisli m a b
           -> CascadeM m (b ': cs)
           -> DebuggerM m zs a (b ': cs)
           -> (a -> m (DebuggerM m (a ': zs) b cs))
        go (Kleisli f) Done         d a = do
          b <- f a
          return $ End d a b
        go (Kleisli f) (f' :>>> fs) d a = do
          b <- f a
          let d' = Break (go f' fs d') d a b
          return d'
