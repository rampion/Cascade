{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE RankNTypes             #-}
module Cascade.Product where
import Cascade

import Control.Arrow (Kleisli(..))
import Control.Comonad (Cokleisli(..), Comonad(..), liftW, (=>>))
import Control.Monad (liftM)
import Control.Monad.Identity (Identity(..))

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

pushes :: (y -> x) -> Product (y ': zs) -> Product (x ': y ': zs)
pushes f yzs@(y :* _) = f y *: yzs
