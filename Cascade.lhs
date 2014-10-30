Over on StackOverflow, Ramith Jayatilleka asked "[What would the type of a
list of cascading functions be?](http://stackoverflow.com/questions/26593237/what-would-the-type-of-a-list-of-cascading-functions-be)"

<blockquote>In Haskell syntax, we can have a (abstract) type like [a -> b],
which is a list of functions a to b. A concrete type of this would be [Int ->
Int], such as map (*) [1..10]. Is it possible to have a list of cascading
functions in a type like [a -> b, b -> c, c -> d, ...]? The individual elements
of the list are all different (I think) so I don't think it's possible. But is
it possible with dependent types? What would its type signature be (preferably
in pseudo-Haskell syntax)?</blockquote>

Under scrambledeggs' answer, Christian Conkle commented:
<blockquote>As I had noted in [my answer to the previous
question](http://stackoverflow.com/a/26566362/1186208), the follow-up
question (and observation) is: what does such a collection give you over
function composition?</blockquote>

So let's try to come up with something that lets us do something **beyond** simple composition.

> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE ConstraintKinds #-}
> {-# LANGUAGE DataKinds #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE GADTs #-}
> {-# LANGUAGE KindSignatures #-}
> {-# LANGUAGE PolyKinds #-}
> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE TypeOperators #-}
> module Cascade where
> import Control.Monad ((>=>), liftM)
> import Control.Comonad ((=>=), liftW, Comonad, extract)
> import Control.Category ((>>>))
> import GHC.Prim (Constraint)
> 
> data Cascade (cs :: [*]) where
>   Done :: Cascade '[a]
>   (:>>>) :: (a -> b) -> Cascade (b ': cs) -> Cascade (a ': b ': cs)
> infixr 5 :>>>
> 
> data Ripple (cs :: [*]) where
>   Apply :: (a -> b) -> Ripple (a ': b ': cs)
>   Skip :: Ripple cs -> Ripple (a ': cs)
> 
> -- you can change part of a cascade
> replaceWith :: Ripple cs -> Cascade cs -> Cascade cs
> replaceWith (Apply f) (_ :>>> fs) = f :>>> fs
> replaceWith (Skip r) (f :>>> fs) = f :>>> replaceWith r fs
> 
> -- generalizing Either to a union of multiple types
> data OneOf (cs :: [*]) where
>   Here :: a -> OneOf (a ': as)
>   There :: OneOf as -> OneOf (a ': as)
> 
> fromHere :: OneOf (a ': as) -> a
> fromHere (Here a) = a
> 
> fromThere :: OneOf (a ': as) -> OneOf as
> fromThere (There o) = o
> 
> -- generalizing (,) to a product of multiple types
> data AllOf (cs :: [*]) where
>   None :: AllOf '[]
>   (:&) :: a -> AllOf as -> AllOf (a ': as)
> infixr 5 :&
> 
> type family AllOf' (cs ::[*]) where
>   AllOf' '[] = ()
>   AllOf' (a ': as) = (a, AllOf' as)
> 
> to :: AllOf cs -> AllOf' cs
> to None = ()
> to (a :& as) = (a, to as)
> 
> -- a small example
> fs :: Cascade '[ String, Int, Float ]
> fs = read :>>> fromIntegral :>>> Done
> 
> -- alternate using functions from one chain then the other
> zigzag :: Cascade as -> Cascade as -> Cascade as
> zigzag Done Done = Done
> zigzag (f :>>> fs) (_ :>>> gs) = f :>>> zigzag gs fs
> 
> -- compose a chain into a single function
> compose :: Cascade (a ': as) -> a -> Last (a ': as)
> compose Done = id
> compose (f :>>> fs) = f >>> compose fs
> 
> -- start the cascade at any of its entry points
> fromOneOf :: Cascade cs -> OneOf cs -> Last cs
> fromOneOf fs (Here a) = compose fs a
> fromOneOf (_ :>>> fs) (There o) = fromOneOf fs o
> 
> -- end the cascade at all of its exit points
> toAllOf :: Cascade (a ': as) -> a -> AllOf (a ': as)
> toAllOf Done a        = a :& None
> toAllOf (f :>>> fs) a = a :& (f >>> toAllOf fs) a
> 
> -- start anywhere, and end everywhere after that
> fromOneOfToAllOf :: Cascade cs -> OneOf cs -> OneOf (Map AllOf (Tails cs))
> fromOneOfToAllOf fs (Here a) = Here $ toAllOf fs a
> fromOneOfToAllOf (_ :>>> fs) (There o) = There $ fromOneOfToAllOf fs o
> 
> -- and you can do Monads too!
> data CascadeM (m :: * -> *) (cs :: [*]) where
>   DoneM :: CascadeM m '[a]
>   (:>=>) :: (a -> m b) -> CascadeM m (b ': cs) -> CascadeM m (a ': b ': cs)
> infixr 5 :>=>
> 
> echo :: CascadeM IO '[(), String, ()]
> echo = const getLine :>=> putStrLn :>=> DoneM
> 
> composeM :: Monad m => CascadeM m (a ': as) -> a -> m (Last (a ': as))
> composeM DoneM = return
> composeM (f :>=> fs) = f >=> composeM fs
> 
> fromOneOfM :: Monad m => CascadeM m cs -> OneOf cs -> m (Last cs)
> fromOneOfM fs (Here a) = composeM fs a
> fromOneOfM (_ :>=> fs) (There o) = fromOneOfM fs o
> 
> -- end the cascade at all of its exit points
> toAllOfM :: Monad m => CascadeM m (a ': as) -> a -> m (AllOf (a ': as))
> toAllOfM DoneM a       = return $ a :& None
> toAllOfM (f :>=> fs) a = (a :&) `liftM` (f >=> toAllOfM fs) a
> 
> -- start anywhere, and end everywhere after that
> fromOneOfToAllOfM :: Monad m => CascadeM m cs -> OneOf cs -> m (OneOf (Map AllOf (Tails cs)))
> fromOneOfToAllOfM fs (Here a) = Here `liftM` toAllOfM fs a
> fromOneOfToAllOfM (_ :>=> fs) (There o) = There `liftM` fromOneOfToAllOfM fs o
> 
> -- and Comonads!
> data CascadeW (w :: * -> *) (cs :: [*]) where
>   DoneW :: CascadeW w '[a]
>   (:=>=) :: (w a -> b) -> CascadeW w (b ': cs) -> CascadeW w (a ': b ': cs)
> infixr 5 :=>=
> 
> composeW :: Comonad w => CascadeW w (a ': as) -> w a -> Last (a ': as)
> composeW DoneW = extract
> composeW (f :=>= fs) = f =>= composeW fs
> 
> fromOneOfW :: Comonad w => CascadeW w cs -> w (OneOf cs) -> Last cs
> fromOneOfW fs w = case extract w of
>   Here _  -> composeW fs $ liftW fromHere w
>   There _ -> case fs of _ :=>= gs -> fromOneOfW gs $ liftW fromThere w
> 
> -- end the cascade at all of its exit points
> toAllOfW :: Comonad w => CascadeW w (a ': as) -> w a -> AllOf (a ': as)
> toAllOfW DoneW w       = extract w :& None
> toAllOfW (f :=>= fs) w = extract w :& (f =>= toAllOfW fs) w
> 
> -- start anywhere, and end everywhere after that
> fromOneOfToAllOfW :: Comonad w => CascadeW w cs -> w (OneOf cs) -> OneOf (Map AllOf (Tails cs))
> fromOneOfToAllOfW fs w = case extract w of
>   Here _  -> Here . toAllOfW fs $ liftW fromHere w
>   There _ -> case fs of _ :=>= gs -> There . fromOneOfToAllOfW gs $ liftW fromThere w
> 
> -- type level list functions
> type family Map (f :: a -> b) (as :: [a]) where
>   Map f '[] = '[]
>   Map f (a ': as) = f a ': Map f as
> 
> type family Last (as :: [a]) where
>   Last '[a] = a
>   Last (a ': as) = Last as
> 
> type family Tails (as :: [a]) where
>   Tails '[] = '[ '[] ]
>   Tails (a ': as) = (a ': as) ': Tails as
> 
> type family Tail (as :: [a]) where
>   Tail (a ': as) = as
> 
> type family Init (as :: [a]) where
>   Init '[a] = '[]
>   Init (a ': as)  = a ': Init as
> 
> type family ZipWith (f :: a -> b -> c) (as :: [a]) (bs :: [b]) where
>   ZipWith f '[] '[] = '[]
>   ZipWith f (a ': as) (b ': bs) = f a b ': ZipWith f as bs
> 
> type family AllEqual (a :: *) (bs :: [*]) :: Constraint where
>   AllEqual a '[] = ()
>   AllEqual a (b ': bs) = (a ~ b, AllEqual a bs)
> 
> {-
> class Equals a b where
> instance a ~ b => Equals a b where
> 
> toList :: All (Equals a) as => AllOf as -> [a]
> -}
> toList :: AllEqual a as => AllOf as -> [a]
> toList None = []
> toList (a :& as) = a : toList as
> 
> type family All (f :: a -> Constraint) (as :: [a]) :: Constraint where
>   All f '[] = ()
>   All f (a ': as) = (f a, All f as)
> 
> {-
> instance All Show as => Show (AllOf as) where
>   show None = "None"
> -}
> 
> instance Show (AllOf '[]) where
>   show None = "None"
> 
> instance (Show a, Show (AllOf as)) => Show (AllOf (a ': as)) where
>   show (a :& as) = show a ++ " :& " ++ show as
> 
>   
> {-
> type Cascade' as = AllOf (ZipWith (->) (Init as) (Tail as))
> 
> to :: Cascade as -> Cascade' as
> to Done = None
> to (f :>>> fs) = f :& to fs
> 
> fro :: Cascade' as -> Cascade as
> fro None = Done
> fro (f :& fs) = f :>>> fro fs
> 
> -- compose a chain into a single function
> compose' :: Cascade' (a ': as) -> a -> Last (a ': as)
> compose' None = id
> --compose' (f :& fs) = f >>> compose' fs
> -}
> -- au BufWritePost *.lhs !pandoc % > %:r.html ; ghc -c %
