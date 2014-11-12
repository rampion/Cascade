{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE TypeOperators          #-}
module Cascade.Operators where
import Control.Category (Category(..))
import Control.Comonad (Comonad(..))
import Cascade.Util.ListKind
import Cascade

(#) :: Category c => CascadeC c (t ': ts) -> c t (Last (t ': ts))
(#) = cascade
infixr 0 #

(#~)  :: Monad m => CascadeM m (t ': ts) -> t -> m (Last (t ': ts))
(#~) = cascadeM
infixr 0 #~

(~#) :: Comonad w => CascadeW w (t ': ts) -> w t -> Last (t ': ts)
(~#) = cascadeW
infixr 0 ~#
