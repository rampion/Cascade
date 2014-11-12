<b>`Cascade`</b>s are collections of composable functions (e.g. `a -> b, b -> c, ... , y -> z`) where the intermediate types are stored in a type level list (e.g. `Cascade [a,b,c,...,y,z]`).

For example, consider these `Cascade`s:

```haskell
fc :: Cascade '[String, Int, Double, Double]
fc =  read          :>>>
      fromIntegral  :>>>
      (1/)          :>>> Done

gc :: Cascade '[String, Int, Double, Double]
gc =  length        :>>>
      (2^)          :>>>
      negate        :>>> Done
```

We can convert a cascade into a function easily enough:

```haskell
λ :m +Cascade.Examples Cascade.Operators
λ fc # "5"
0.2
λ gc # "20"
-4.0
```

But that's not very inspiring. The real question, [as Christian Conkle put it](http://stackoverflow.com/questions/26593237/what-would-the-type-of-a-list-of-cascading-functions-be#comment41802812_26593534), is "what does such a collection give you over function composition?"

Because none of the type information has been lost, we can still extract each of the functions that went into the `Cascade` using simple pattern matching. This opens the door to replacing parts of a cascade, or indexing into the cascade with type-level naturals.

It also lets us do something silly like mix and match two different cascades:

```haskell
λ zigzag fc gc # "3" -- read >>> (2^) >>> (1/)
0.125
λ zigzag gc fc # "123456789" -- length >>> fromIntegral >>> negate
-9.0
```

More seriously, we can record the intermediate results of each `Cascade` using a `Product` type as output:

```haskell
λ :m +Cascade.Product
λ record fc # "5" *: None
0.2 *: 5.0 *: 5 *: "5" *: None
λ record gc # "5" *: None
-2.0 *: 2.0 *: 1 *: "5" *: None
```

Or I can resume the computation at some later point rather that the first function in the `Cascade` using a `Sum` type as input:

```haskell
λ :m +Cascade.Sum
λ resume fc # (there.there.here) 0.2
here 5.0
λ resume gc # (there.here) 0
here (-1.0)
```

Or we could do both:

```haskell
λ resume (record fc) # (there.here) (17 *: "foo" *: None)
here (5.8823529411764705e-2 *: 17.0 *: 17 *: "foo" *: None)
λ record (resume fc) # (there . there $ here 0.25) *: None
here 4.0 *: here 0.25 *: (there.here $ 0.25) *: (there.there.here $ 0.25) *: None
```

But what's nice is that this generalizes nicely to categorical composition, so we can do the same with 
any categroy, including the `Kleisli` and `Cokleisli` categories for `Monad`s and `Comonad`s respectfully:

```haskell
-- some example monadic cascades
mc, nc :: CascadeM IO '[ String, (), String, String, () ]
mc =  putStr                  >=>:
      const getLine           >=>:
      return . map toUpper    >=>:
      putStrLn                >=>: Done
nc =  setEnv "foo"            >=>: 
      const (return "foo")    >=>:
      getEnv                  >=>:
      print . length          >=>: Done
```

```haskell
-- some example comonadic cascades
wc, vc :: CascadeW ((,) Char) '[ Int, Char, Int, String ]
wc =  fst                       =>=:
      fromEnum . snd            =>=:
      uncurry (flip replicate)  =>=: Done
vc =  toEnum . snd              =>=:
      const 5                   =>=:
      show                      =>=: Done
```

Flipping back to ghci:

```haskell
λ mc #~ "? "
? i like cheese
I LIKE CHEESE
λ nc #~ "? "
2
λ wc ~# ('.', 5)
".............................................."
λ vc ~# ('x', 9)
"('x',5)"
λ zigzag mc nc #~ "hi!"
hi!3
λ zigzag nc mc #~ "hello."
USER
rampion
λ zigzag wc vc ~# ('.', 3)
"....."
λ zigzag vc wc ~# ('a', 9)
"('a',9)"
```

`resume` works on both comonads and monads:

```haskell
λ resumeM nc #~ (there.there.here) "USER"
7
here ()
λ toEither $ resumeW vc # (There . There . Here) ('c',9)
Left ('c',"('c',9)")
```

`record` works on comonads, but I've been having some issues getting it to work the way I want on monads (see `Cascade.Product.hs` for more).

So, instead of continue to wrestle the type system, for now, I just implemented a debugger that uses `Cascade`s,
so in addition running a monadic `Cascade` you can debug it.

```haskell
-- run the debugger for the mc cascade all the way to the end
rundmc :: IO (DebuggerM IO '[String, String, (), [Char]] () '[])
rundmc = debugM >>> use "walk this way\n> " >=> step >=> step >=> step $ mc
```

Dropping into ghci:

```haskell
λ d <- rundmc
walk this way
> talk this way
TALK THIS WAY
```

We can see the current state of the debugger:

```haskell
λ d
End   { given = "TALK THIS WAY", returned = () }
```

the full stack trace

```haskell
λ printHistory d
End   { given = "TALK THIS WAY", returned = () }
Break { given = "talk this way", returned = "TALK THIS WAY" }
Break { given = (), returned = "talk this way" }
Break { given = "walk this way\n> ", returned = () }
Begin
```

back up, step forward:

```haskell
λ back d
Break { given = "talk this way", returned = "TALK THIS WAY" }
λ back it
Break { given = (), returned = "talk this way" }
λ step it
Break { given = "talk this way", returned = "TALK THIS WAY" }
λ step it
TALK THIS WAY
End   { given = "TALK THIS WAY", returned = () }
```

(Note that when we step forward, the monadic computation reruns)

We can also use a different input than the default at the current stage:

```haskell
λ back d
Break { given = "talk this way", returned = "TALK THIS WAY" }
λ d' <- use "(talk this way)" it
(talk this way)
λ printHistory d'
End   { given = "(talk this way)", returned = () }
Break { given = "talk this way", returned = "TALK THIS WAY" }
Break { given = (), returned = "talk this way" }
Break { given = "walk this way\n> ", returned = () }
Begin
```

And since the debuggers are normal immutable haskell values, we can use both `d` and `d'` without errors.

---

`Cascade`s are still very limited. They're linear, and of a set length. They don't let you hook into functions that call themselves recursively, or functions that have computation paths better represented by trees or lattices.

But that doesn't mean those are necessarily impossible to model, either. For example, simple recursion is fairly easily captured with only a slight modification to `Cascade`

```haskell
data CascadeR (ts :: [*]) where
  (:>>>)  :: x -> y -> CascadeR (y ': zs) -> CascadeR (x ': y ': zs)
  Fix     :: ((x -> y) -> x -> y) -> CascadeR (y ': zs) -> CascadeR (x ': y ': zs)
  Done    :: CascadeR '[t]
```

