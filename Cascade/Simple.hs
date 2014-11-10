{-# LANGUAGE DataKinds            #-}
{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE GADTs                #-}
{-# LANGUAGE KindSignatures       #-}
{-# LANGUAGE TypeFamilies         #-}
{-# LANGUAGE TypeOperators        #-}
{-# LANGUAGE UndecidableInstances #-}
module Simple where

ex_p :: Product '[String, Int, Double, Double]
ex_p = "Hello" :* 5 :* 5.0 :* 0.2 :* None

ex_s :: Sum '[String, Int, Double, Double]
ex_s = There $ Here 5

ex_c :: Cascade '[String, Int, Double, Double]
ex_c =  length        :>>>
        fromIntegral  :>>>
        (1/)          :>>> Done

-- generalized product
--  Product '[]      =~ ()
--  Product '[a]     =~ (a, ())
--  Product '[a,b]   =~ (a, (b, ()))
--  Product '[a,b,c] =~ (a, (b, (c, ())))
data Product (ts :: [*]) where
  None :: Product '[]
  (:*) :: a -> Product ts -> Product (a ': ts)
infixr 5 :*

instance Show (Product '[]) where
  showsPrec _ None = showString "None"

instance (Show a, Show (Product as)) => Show (Product (a ': as)) where
  showsPrec p (a :* as) = showParen (p > 10) $ showsPrec 5 a . showString " :* " . showsPrec 5 as

-- generalized sum
--  Sum '[]         =~ Void
--  Sum '[a]        =~ a
--  Sum '[a,b]      =~ Either a b
--  Sum '[a,b,c]    =~ Either a (Either b c)
--  Sum '[a,b,c,d]  =~ Either a (Either b (Either c d))
data Sum (ts :: [*]) where
  Here  :: a -> Sum (a ': as)
  There :: Sum as -> Sum (a ': as)

instance Show (Sum '[]) where
  showsPrec _ s = seq s $ error "impossible value of type OneOf '[]"

instance (Show a, Show (Sum as)) => Show (Sum (a ': as)) where
  showsPrec p (Here a)    = showParen (p > 10) $ showString "Here " . showsPrec 11 a
  showsPrec p (There as)  = showParen (p > 10) $ showString "There " . showsPrec 11 as

-- reified functional composition
--  Cascade '[a]       =~ Product '[]                         =~ a -> a
--  Cascade '[a,b]     =~ Product '[ a -> b ]                 =~ a -> b
--  Cascade '[a,b,c]   =~ Product '[ a -> b, b -> c ]         =~ a -> c
--  Cascade '[a,b,c,d] =~ Product '[ a -> b, b -> c, c -> d ] =~ a -> d
data Cascade (ts :: [*]) where
  (:>>>)  :: (x -> y) -> Cascade (y ': zs) -> Cascade (x ': y ': zs)
  Done    :: Cascade '[t]
infixr 1 :>>>

-- convert a cascade into a function
{-
cascade0 :: Cascade '[a] -> a -> a
cascade0 Done = id

cascade1 :: Cascade '[a,b] -> a -> b
cascade1 (f :>>> fs) = cascade0 fs . f

cascade2 :: Cascade '[a,b,c] -> a -> c
cascade2 (f :>>> fs) = cascade1 fs . f
-}

type family Last (ts :: [*]) :: * where
  Last '[a] = a
  Last (a ': bs) = Last bs

-- compress into a function
cascade :: Cascade (t ': ts) -> t -> (Last (t ': ts))
cascade Done = id
cascade (f :>>> fs) = cascade fs . f

-- run a function if necessary to get rid of any possible `a` value
pops :: (a -> b) -> Sum (a ': b ': cs) -> Sum (b ': cs)
pops f (Here a)   = Here $ f a
pops f (There s)  = s

resumes0 :: Cascade '[ a ] -> Cascade '[ Sum (a ': ts) ]
resumes0 Done = Done

resumes1 :: Cascade '[ a, b ] -> Cascade '[ Sum ( a ': b ': cs), Sum ( b ': cs) ]
resumes1 (f :>>> fs) = pops f :>>> resumes0 fs

resumes2 :: Cascade '[ a, b, c ] -> Cascade '[ Sum ( a ': b ': c ': ds), Sum ( b ': c ': ds), Sum (c ': ds ) ]
resumes2 (f :>>> fs) = pops f :>>> resumes1 fs

-- TODO: properly should be TailMaps f ts ts' with i
--  TailMaps f (a ': as) ts' = Sum (a ': Concat as ts') ': TailMaps f as ts'
type family TailMaps (f :: [*] -> *) (ts :: [*]) :: [*] where
  TailMaps f '[] = '[]
  TailMaps f (a ': as) = f (a ': as) ': TailMaps f as

resumes :: Cascade ts -> Cascade (TailMaps Sum ts)
resumes Done = Done
resumes (f :>>> fs) = pops f :>>> resumes fs

-- run a function, leaving its input and output on top of a stack
pushes :: (y -> x) -> Product (y ': zs) -> Product (x ': y ': zs)
pushes f yzs@(y :* _) = f y :* yzs

{-
records0 :: Cascade '[ w ] -> Cascade '[ Product (w ': xs) ]
records0 Done = Done

records1 :: Cascade '[ x, w ] -> Cascade '[ Product (x ': ys),  Product (w ': x ': ys) ]
records1 (f :>>> fs) = pushes f :>>> records0 fs

records2 :: Cascade '[ y,x,w ] -> Cascade '[ Product (y':zs), Product (x':y':zs), Product (w':x':y':zs) ]
records2 (f :>>> fs) = pushes f :>>> records1 fs
-}

type family RInitProducts (ts :: [*]) (ts' :: [*]) :: [*] where
  RInitProducts (a ': as) ts' = Product (a ': ts') ': RInitProducts as (a ': ts')
  RInitProducts '[] ts' = '[]

records :: Cascade (t ': ts) -> Cascade (RInitProducts (t ': ts) ts')
records Done = Done
records (f :>>> fs) = pushes f :>>> records fs

data RCascade (ts :: [*]) where
  (:.)  :: (x -> y) -> RCascade (x ': zs) -> RCascade (y ': x ': zs)
  RDone :: RCascade '[t]
infixr 1 :.

data RProduct (ts :: [*]) where
  RNone :: RProduct '[]
  (:/) :: (ts' ~ Concat ts '[a], a ~ Last ts', ts ~ Init ts') => RProduct ts -> a -> RProduct ts'
infixl 5 :/

type family Init (as :: [*]) where
  Init '[a] = '[]
  Init (a ': as)  = a ': Init as

type family RConcat (ts :: [*]) (ts' :: [*]) :: [*] where
  RConcat '[] ts' = ts'
  RConcat (t ': ts) ts' = RConcat ts (t ': ts')

type family Concat (ts :: [*]) (ts' :: [*]) :: [*] where
  Concat '[] ts' = ts'
  Concat (t ': ts) ts' = t ': Concat ts ts'

replays0 :: RCascade '[ w ] -> RCascade '[ RProduct (w ': ts) ]
replays0 RDone = RDone

replays1 :: RCascade '[ x, w ] -> RCascade '[ RProduct (x ': w ': vs ), RProduct (w ': vs) ]
replays1 (f :. fs) = unshifts f :. replays0 fs

unshifts :: (y -> x) -> RProduct (y ': zs) -> RProduct (x ': y ': zs)
unshifts f (RNone :/ y) = RNone :/ f y :/ y
unshifts f (ys@(_ :/ _) :/ z) = unshifts f ys :/ z

unshifts1 :: (y -> x) -> RProduct '[y] -> RProduct '[x,y]
unshifts1 f (RNone :/ y) = RNone :/ f y :/ y

unshifts2 :: (y -> x) -> RProduct '[y,z] -> RProduct '[x,y,z]
unshifts2 f ( ys@(_ :/ _) :/ z) = unshifts1 f ys :/ z

unshifts3 :: (y -> x) -> RProduct '[y,z,a] -> RProduct '[x,y,z,a]
unshifts3 f ( ys@(_ :/ _) :/ z) = unshifts2 f ys :/ z

{-
replays2 :: RCascade '[ y, x, w ] -> RCascade '[ Product (y ': x ': w ': vs ), Product (x ': w ': vs ), Product (w ': vs) ]
replays2 (f :. fs) = pushes f :. replays1 fs
-}

replaysR :: RCascade ts -> RCascade (TailMaps Product ts)
replaysR RDone = RDone
replaysR ( f :. fs ) = pushes f :. replaysR fs

replays :: TailMaps Product (RConcat ts1 '[t1]) ~ (t ': ts) =>
   Cascade (t1 ': ts1) -> Cascade (RConcat ts '[t])
replays = deverses . replaysR . reverses

reverses :: Cascade (t ': ts) -> RCascade (RConcat ts '[t])
reverses = reversesOnto RDone

reversesOnto :: RCascade (t ': ts') -> Cascade (t ': ts) -> RCascade (RConcat ts (t ': ts'))
reversesOnto c Done = c
reversesOnto c (f :>>> fs) = reversesOnto (f :. c) fs 

deverses :: RCascade (t ': ts) -> Cascade (RConcat ts '[t])
deverses = deversesOnto Done

deversesOnto :: Cascade (t ': ts') -> RCascade (t ': ts) -> Cascade (RConcat ts (t ': ts'))
deversesOnto c RDone = c
deversesOnto c (f :. fs) = deversesOnto (f :>>> c) fs
