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

> {-# LANGUAGE ConstraintKinds        #-}
> {-# LANGUAGE DataKinds              #-}
> {-# LANGUAGE FlexibleContexts       #-}
> {-# LANGUAGE FlexibleInstances      #-}
> {-# LANGUAGE GADTs                  #-}
> {-# LANGUAGE KindSignatures         #-}
> {-# LANGUAGE MultiParamTypeClasses  #-}
> {-# LANGUAGE PolyKinds              #-}
> {-# LANGUAGE TypeFamilies           #-}
> {-# LANGUAGE TypeOperators          #-}
> module Cascade where
> import Control.Monad    ((>=>), liftM)
> import Control.Comonad  ((=>=), liftW, Comonad, extract)
> import Control.Category ((>>>))
> import GHC.Prim         (Constraint)

What we need is a type that instead of just recording the initial and final types of 
the cascade of functions, records the type of each intermediate value as well.

We can do this by using a GADT parameterized by a type-level list:

> data Cascade (cs :: [*]) where
>   Done :: Cascade '[a]
>   (:>>>) :: (a -> b) -> Cascade (b ': cs) -> Cascade (a ': b ': cs)
> infixr 5 :>>>

Note that we check that the output of the function we cons with a `Cascade`
matches the input to the `Cascade`.

To see how these work, we'll need some way to apply them:

> -- convert a Cascade to a function
> compose :: Cascade (a ': as) -> a -> Last (a ': as)
> compose Done = id
> compose (f :>>> fc) = f >>> compose fc
>
> (~$~) = compose
>
> -- type level version of last :: [a] -> a
> type family Last (as :: [a]) where
>   Last '[a] = a
>   Last (a ': as) = Last as

So now we can construct cascades of functions:

> fc, gc :: Cascade '[ String, Int, Float ]
> fc = read :>>> fromIntegral :>>> Done
> gc = length :>>> (2^) :>>> Done

And apply them:

    λ fc ~$~ "10"
    10.0
    λ gc ~$~ "10"
    4.0

But that's no more than we can do with function composition. What else can we do?

How about blending two cascades?

> -- alternate using functions from one cascade then the other
> zigzag :: Cascade as -> Cascade as -> Cascade as
> zigzag Done Done = Done
> zigzag (f :>>> fc) (_ :>>> gc) = f :>>> zigzag gc fc

    λ zigzag fc gc ~$~ "10"
    1024.0
    λ zigzag gc fc ~$~ "10"
    2.0

Or replacing one part of a cascade with a different function of the same type?

> data Ripple (cs :: [*]) where
>   Apply :: (a -> b) -> Ripple (a ': b ': cs)
>   Skip :: Ripple cs -> Ripple (a ': cs)
> 
> replaceWith :: Ripple cs -> Cascade cs -> Cascade cs
> replaceWith (Apply f) (_ :>>> fc) = f :>>> fc
> replaceWith (Skip r) (f :>>> fc) = f :>>> replaceWith r fc
>
> zr :: Ripple (a ': b ': Float ': cs)
> zr = Skip . Apply $ const 0.0

    λ replaceWith zr fc ~$~ "10"
    0.0
    λ replaceWith zr gc ~$~ "10"
    0.0

More usefully, we can also use a cascade to see all the intermediate results :

> -- generalizing (,) to a product of multiple types
> data AllOf (cs :: [*]) where
>   None :: AllOf '[]
>   (:&) :: a -> AllOf as -> AllOf (a ': as)
> infixr 5 :&
>
> instance Show (AllOf '[]) where
>   showsPrec _ None = showString "None"
> 
> instance (Show a, Show (AllOf as)) => Show (AllOf (a ': as)) where
>   showsPrec p (a :& as) = showParen (p > 10) $ showsPrec 5 a . showString " :& " . showsPrec 5 as
> 
> -- end the cascade at all of its exit points
> toAllOf :: Cascade (a ': as) -> a -> AllOf (a ': as)
> toAllOf Done a        = a :& None
> toAllOf (f :>>> fc) a = a :& (f >>> toAllOf fc) a
>
> (*$~) = toAllOf

    λ fc *$~ "10"
    "10" :& 10 :& 10.0 :& None
    λ gc *$~ "10"
    "10" :& 2 :& 4.0 :& None

Or to resume a computation from any point:

> -- generalizing Either to a union of multiple types
> data OneOf (cs :: [*]) where
>   Here :: a -> OneOf (a ': as)
>   There :: OneOf as -> OneOf (a ': as)
> 
> instance Show (OneOf '[]) where
>   showsPrec _ _ = error "impossible value of type OneOf '[]"
> 
> instance (Show a, Show (OneOf as)) => Show (OneOf (a ': as)) where
>   showsPrec p (Here a)    = showParen (p > 10) $ showString "Here " . showsPrec 11 a
>   showsPrec p (There as)  = showParen (p > 10) $ showString "There " . showsPrec 11 as
> 
> -- start the cascade at any of its entry points
> fromOneOf :: Cascade cs -> OneOf cs -> Last cs
> fromOneOf fc (Here a) = compose fc a
> fromOneOf (_ :>>> fc) (There o) = fromOneOf fc o
>
> (~$?) = fromOneOf

    λ fc ~$? Here "70"
    70.0
    λ gc ~$? There (Here 5)
    32.0

Or both:

> -- start anywhere, and end everywhere after that
> fromOneOfToAllOf :: Cascade cs -> OneOf cs -> OneOf (Map AllOf (Tails cs))
> fromOneOfToAllOf fc (Here a) = Here $ toAllOf fc a
> fromOneOfToAllOf (_ :>>> fc) (There o) = There $ fromOneOfToAllOf fc o
>
> (*$?) = fromOneOfToAllOf

    λ fc *$? There (Here 70)
    There (Here (70 :& 70.0 :& None))
    λ gc *$? Here "six"
    Here ("six" :& 3 :& 8.0 :& None)

> 
> type family AllOf' (cs ::[*]) where
>   AllOf' '[] = ()
>   AllOf' (a ': as) = (a, AllOf' as)
> 
> to :: AllOf cs -> AllOf' cs
> to None = ()
> to (a :& as) = (a, to as)
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
> composeM (f :>=> fc) = f >=> composeM fc
> 
> fromOneOfM :: Monad m => CascadeM m cs -> OneOf cs -> m (Last cs)
> fromOneOfM fc (Here a) = composeM fc a
> fromOneOfM (_ :>=> fc) (There o) = fromOneOfM fc o
> 
> -- end the cascade at all of its exit points
> toAllOfM :: Monad m => CascadeM m (a ': as) -> a -> m (AllOf (a ': as))
> toAllOfM DoneM a       = return $ a :& None
> toAllOfM (f :>=> fc) a = (a :&) `liftM` (f >=> toAllOfM fc) a
> 
> -- start anywhere, and end everywhere after that
> fromOneOfToAllOfM :: Monad m => CascadeM m cs -> OneOf cs -> m (OneOf (Map AllOf (Tails cs)))
> fromOneOfToAllOfM fc (Here a) = Here `liftM` toAllOfM fc a
> fromOneOfToAllOfM (_ :>=> fc) (There o) = There `liftM` fromOneOfToAllOfM fc o
> 
> -- and Comonads!
> data CascadeW (w :: * -> *) (cs :: [*]) where
>   DoneW :: CascadeW w '[a]
>   (:=>=) :: (w a -> b) -> CascadeW w (b ': cs) -> CascadeW w (a ': b ': cs)
> infixr 5 :=>=
> 
> composeW :: Comonad w => CascadeW w (a ': as) -> w a -> Last (a ': as)
> composeW DoneW = extract
> composeW (f :=>= fc) = f =>= composeW fc
> 
> fromHere :: OneOf (a ': as) -> a
> fromHere (Here a) = a
> 
> fromThere :: OneOf (a ': as) -> OneOf as
> fromThere (There o) = o
> 
> fromOneOfW :: Comonad w => CascadeW w cs -> w (OneOf cs) -> Last cs
> fromOneOfW fc w = case extract w of
>   Here _  -> composeW fc $ liftW fromHere w
>   There _ -> case fc of _ :=>= gc -> fromOneOfW gc $ liftW fromThere w
> 
> -- end the cascade at all of its exit points
> toAllOfW :: Comonad w => CascadeW w (a ': as) -> w a -> AllOf (a ': as)
> toAllOfW DoneW w       = extract w :& None
> toAllOfW (f :=>= fc) w = extract w :& (f =>= toAllOfW fc) w
> 
> -- start anywhere, and end everywhere after that
> fromOneOfToAllOfW :: Comonad w => CascadeW w cs -> w (OneOf cs) -> OneOf (Map AllOf (Tails cs))
> fromOneOfToAllOfW fc w = case extract w of
>   Here _  -> Here . toAllOfW fc $ liftW fromHere w
>   There _ -> case fc of _ :=>= gc -> There . fromOneOfToAllOfW gc $ liftW fromThere w
> 
> -- type level list functions
> type family Map (f :: a -> b) (as :: [a]) where
>   Map f '[] = '[]
>   Map f (a ': as) = f a ': Map f as
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
>   
> {-
> type Cascade' as = AllOf (ZipWith (->) (Init as) (Tail as))
> 
> to :: Cascade as -> Cascade' as
> to Done = None
> to (f :>>> fc) = f :& to fc
> 
> fro :: Cascade' as -> Cascade as
> fro None = Done
> fro (f :& fc) = f :>>> fro fc
> 
> -- compose a cascade into a single function
> compose' :: Cascade' (a ': as) -> a -> Last (a ': as)
> compose' None = id
> --compose' (f :& fc) = f >>> compose' fc
> -}
> -- au BufWritePost *.lhs !pandoc % > %:r.html ; ghc -c %
