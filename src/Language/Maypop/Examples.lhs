In this module, we'll use the syntax definitions from the `Syntax` module to
define a few example terms. This should make it more convenient to ensure
that the code is still operating as expected.

> module Language.Maypop.Examples where
> import Language.Maypop.Syntax
> import Language.Maypop.Modules
> import qualified Data.Map as Map

For convenience, we'll use `p` to referm to the term `Prop`, and `t n` to refer
to the term `Sort (Type n)`.

> p = Sort Prop
> t = Sort . Type

In the absense of concrete types, the simplest term I can think of is the polymorphic
identity function. This function takes its argument type as input first, then an argument
of that type, and returns the argument unchanged. Mathematically, and without
using DeBrujin indices, this function could be written as:

\$$
\\text{id} = \\lambda (\\alpha : \\text{Type 0}).\\lambda (a : \\alpha). a
\$$

Then, it is applied as \\(\\text{id} \\ \\mathbb{N} \\ 3\\), which evaluates to \\(3\\).

> id_ :: Term
> id_ = Abs (t 0) $ Abs (Ref 0) $ Ref 0

In a similar vein, we can define Haskell's `const` function. Much like the identity function,
it does not require any other data types, and does not need to look into its arguments. The
Haskell signature of this function is `a -> b -> a`; there are _two_ types that are in
play here, and the mathematical definition of the function is to match:

\$$
\\text{const} = \\lambda (\\alpha : \\text{Type 0}). \\lambda (\\beta : \\text{Type 0}). \\lambda (a : \\alpha). \\lambda (b : \\beta). a
\$$

Since `const` is in the Haskell Prelude, and since it's a useful function that we don't want
to shadow, we once again add an underscore to the name of the Maypop term. The entire
definition is as follows:

> const_ :: Term
> const_ = Abs (t 0) $ Abs (t 0) $ Abs (Ref 1) $ Abs (Ref 1) $ Ref 1

Let's have an example of function application for once. Why not apply
the identity function to `Prop`? We'll need to define a type-level
identity function since `id_` can only accept type parameters of type `Type 0`,
but our type parameter here _will be_ `Type 0`, a type parameter of type `Type 1`.

> id_' :: Term
> id_' = Abs (t 1) $ Abs (Ref 0) $ Ref 0
> 
> idProp :: Term
> idProp = App (App id_' (t 0)) p

We'll be writing function applications a lot. This will get cumbersome, especially
since we'll have to be explicitly passing type parameters to any polymorphic function.
To save ourselves the burden of writing these applications using chains of `App`s,
let's define some meta-notation: \\(\\underline{\\text{apps}}\\). We define
it as follows:

```
apps t [t1, ..., tn] = App (App (App t t1) ...) tn
```

This is a straightforward left fold:

> apps :: Term -> [Term] -> Term
> apps = foldl App

There's only so much you can do by using the pure Calculus of Constructions.
What about the _Inductive_ part? Let's define some basic inductive data types?
Here's one for natural numbers.

> nat :: Inductive
> nat = Inductive
>     { iParams = []
>     , iArity = []
>     , iSort = Type 0
>     , iName = "ℕ"
>     , iConstructors =
>         [ Constructor { cParams = [], cIndices = [], cName = "O" }
>         , Constructor { cParams = [ Ind nat ], cIndices = [], cName = "S" }
>         ]
>     }

This is a lot of code, for what seems like a very basic data type! Well,
natural numbers are not _parameterized_ by anything, and nor are they _indexed_
by anything, so both `iParams` and `iArity` are empty. The type of natural numbers,
which we'll denote \\(\\mathbb{N}\\), is itself of sort \\(\\text{Type 0}\\).
Finally, this type has two constructors: `O`, which represents zero and takes
no parameters, and `S`, which
{{< sidenote "right" "debrujin-note" "takes another natural number as a parameter," >}}
The parameter is unnamed here because we use DeBrujin indices; however,
it occurs in the <code>cParams</code> field of the second constructor.
{{< /sidenote >}}
and returns its succesor.

We can define a few quick shortcuts for writing down natural numbers. We'll
use `n` to convert a Haskell `Int` into a natural number, `s` to refer to the
natural succsessor function, and `o` to refer to the natural zero.

> n :: Int -> Term
> n 0 = Constr nat 0
> n m = App (Constr nat 1) $ n (m-1)
>
> s :: Term -> Term
> s = App (Constr nat 1)
>
> o :: Term
> o = Constr nat 0

Natural numbers can be written down in pretty much any language. A more interesting
data type is that of _finite_ natural numbers. They are indexed by a natural number,
and `Fin` is thus a type constructor; the type `Fin n` represents "natural numbers
less than `n`". This data type has two constructors, which correspond quite closely
to those of the natural numbers: `FZ` and `FS`. Just like `O`, `FZ` represents
zero; however, there are _many possible zeroes_! There's a zero less than 1, a zero
less than 2, 
{{< sidenote "right" "zero-note" "and so on." >}}
It doesn't matter that these zeroes represent the same number; they are inhabitants
of different types, and are therefore different to the type system.
{{< /sidenote >}}
The `FZ` constructor, then, needs to take the exact natural number as argument.
Thus, we have \\(\\text{FZ} : \\forall (n : \\mathbb{N}). \\text{Fin} \\ n\\).
A similar story applies to the `FS` constructor; however, unlike `FZ`, it takes
another number, and represents that number's successor. We know from math that
if \\(f < n\\), then \\(f + 1 < n + 1\\). By the same token, if \\(f : \\text{Fin} \\ n\\),
then \\(\\text{FS} \\ f : \\text{Fin} \\ (S \\ n)\\). Overall, we have
\\(\\text{FS} : \\forall (n : \\mathbb{N}). \\text{Fin} \\ n \\rightarrow \\text{Fin} \\ (S \\ n)\\).
This is the code we end up with:

> fin :: Inductive
> fin = Inductive
>     { iParams = []
>     , iArity = [ Ind nat ]
>     , iSort = Type 0
>     , iName = "Fin"
>     , iConstructors =
>         [ Constructor { cParams = [ Ind nat ], cIndices = [ s (Ref 0) ], cName = "FZ" }
>         , Constructor { cParams = [ Ind nat, App (Ind fin) (Ref 0) ], cIndices = [ App (Constr nat 1) (Ref 1) ], cName = "FS" }
>         ]
>     }

Once again, we could use some shortcuts. We'll use `fz n` to create a bounded zero
that's less than `n`, and `fs n` to create the successor function expecting an
argument less than `n`.

> fz :: Term -> Term
> fz = App (Constr fin 0)
> 
> fs :: Term -> Term -> Term
> fs m = App (App (Constr fin 1) m)

Let's also define an either data type. This type has two type parameters, which signify the
types of the can be contained in it. `Either A B` can be either `Left x` for `x : A` or `Right y`,
with `y : B`. In short, `Either` is effectively a coproduct, or sum type.

> either_ :: Inductive
> either_ = Inductive
>     { iParams = [t 0, t 0]
>     , iArity = []
>     , iSort = Type 0
>     , iName = "Either"
>     , iConstructors =
>         [ Constructor { cParams = [Ref 1], cIndices = [], cName = "Left" }
>         , Constructor { cParams = [Ref 0], cIndices = [], cName = "Right" }
>         ]
>     }

As before, it's nice to have Haskell functions to actually reference
the constructors of the new data type. We'll define `inl`, which
is the application of `Left` to first the two types parameters of the either type,
and then a value of the first (left) type. Symmetrically, `inr`
will be the application of `Right` first to the two types parameters of the either type,
and then a value of the second (right) type.

> inl :: Term -> Term -> Term -> Term
> inl t1 t2 a = foldl App (Constr either_ 0) [t1, t2, a]
>
> inr :: Term -> Term -> Term -> Term
> inr t1 t2 a = foldl App (Constr either_ 1) [t1, t2, a]

The dual of a sum type is a product type, also known as a pair type. This
type also has two type parameters, but it only has a single constructor,
which contains values of _both_ types.

> pair_ :: Inductive
> pair_ = Inductive
>     { iParams = [t 0, t 0]
>     , iArity = []
>     , iSort = Type 0
>     , iName = "Pair"
>     , iConstructors =
>         [ Constructor { cParams = [Ref 1, Ref 1], cIndices = [], cName = "MkPair" }
>         ]
>     }

This type's single constructor is translated into the Haskell helper function `mkPair`,
which takes the two type parameters of the pair type, and then the two values of
these respective types.

> mkPair :: Term -> Term -> Term -> Term -> Term
> mkPair t1 t2 v1 v2 = foldl App (Constr pair_ 0) [t1,t2,v1,v2]

Let's do a little bit of pattern matcing, shall we? One of the simplest
functions we can implement on data types is the predecessor function for
natural numbers. Unlike the various helper functions for constructors,
we'll actually define it as a lambda abstraction. This way we can pass
it around without issue (and check its type!)

> pred_ :: Term
> pred_ = Abs (Ind nat) $ Case (Ref 0) nat (Ind nat) [n 0, Ref 0]

We can define a similar function for bounded natural numbers. There's
a catch: we can't take the predecessor of a number that's _less than zero_.
In fact, it arguably doesn't make sense to take the predecessor of a number
that's less than one. We thus require an input number less than \\(n+2\\), and
return a natural number less than \\(n+1\\).

> predFin :: Term
> predFin = Abs (Ind nat) $ Abs (App (Ind fin) $ s $ s (Ref 0)) $ Case (Ref 0) fin (App (Ind fin) $ s (Ref 3)) [fz (Ref 2)]  -- FS case doesn't work

A fairly interesting function on the `Either` data type is to extract whatever is
inside the `Either`. This can only work if both the "left" and "right" types match
up, which makes this function accept exactly one type parameter (and passing that type
parameter twice to the `Either` type constructor).

> unwrapEither :: Term
> unwrapEither = Abs (t 0) $ Abs (App (App (Ind either_) (Ref 0)) (Ref 0)) $ Case (Ref 0) either_ (Ref 2) [Ref 0, Ref 0]

For pairs, a simple operation we can implement in the `swap` function, which turns
a pair like `(1,"Hello")` into a pair like `("Hello", 1)`. This function is our
most tedious yet, since it must actually use its type parameters for more than
naming the type of its input value. Indeed, the type parameters must be fed
-- in a different order -- to the `MkPair` constructor used to create
the return value.

> swap_ :: Term
> swap_ = Abs (t 0) $ Abs (t 0) $ Abs (App (App (Ind pair_) (Ref 1)) (Ref 0)) $ Case (Ref 0) pair_ (App (App (Ind pair_) (Ref 2)) (Ref 3)) [ mkPair (Ref 3) (Ref 4) (Ref 0) (Ref 1) ]

Now that we have these functions, let's write down some examples. Our first few will be applications
of our new functions to concrete values and types:

* \\(\\text{ex1} = \\text{pred} \\ 3\\), which should evaluate to \\(2\\).
* \\(\\text{ex2} = \\text{prefFin} \\ (2 : \\text{Fin} \\ 4) \\), which should evaluate to \\(1 : \\text{Fin} \\ 3\\).
* \\(\\text{ex3} = \\text{unwrapEither} \\ (\\text{Left} \\ 3)\\), which should evaluate to \\(3\\).
* \\(\\text{ex4} = \\text{swap} \\ (3, 2)\\), which should evaluate to \\((2,3)\\).

> ex1 :: Term
> ex1 = App pred_ (n 3)
>
> ex2 :: Term
> ex2 = apps predFin [n 2, fs (n 3) $ fs (n 2) $ fz (n 1)]
>
> ex3 :: Term
> ex3 = apps unwrapEither [Ind nat, inl (Ind nat) (Ind nat) (n 3)]
>
> ex4 :: Term
> ex4 = apps swap_ [Ind nat, Ind nat, mkPair (Ind nat) (Ind nat) (n 3) (n 2)]

An interesting thing we could try to define is an _abstract data type_. We can do this
by making the _constructor_ of the type be parameterized by some type, without parameterizing
the type itself. For instance, we can define a `Countable` data type:

> countable :: Inductive
> countable = Inductive
>     { iParams = []
>     , iArity = []
>     , iSort = Type 0
>     , iName = "Countable"
>     , iConstructors =
>         [ Constructor { cParams = [t 0, (Ref 0), Prod (Ref 1) (Ind nat)], cIndices = [], cName = "Wrap" }
>         ]
>     }

Once we pass it the type, that type is "gone". There are no guarantees we can make about
it once we pattern match on, and unpack, an instance of `Countable`. All we'll know is
that it's some type `a`, for which there is some value `x : a` and a function `f : a -> Nat`.
This is our abstraction: no further information escapes from the data type. As usually, let's
define a Haskell function to make it easier to call the `Wrap` constructor:

> wrap :: Term -> Term -> Term -> Term
> wrap t x f = apps (Constr countable 0) [t, x, f]

If we can wrap, we can also unwrap. Without leaking the inner type (which we could
do with a dependent pair, I suppose), the only thing we _really_ do is apply our
counting function `f` to our wrapped value `x`, and return the result. Let's
define `count` to do just that:

> count :: Term
> count = Abs (Ind countable) $ Case (Ref 0) countable (Ind nat) [App (Ref 0) (Ref 1)]

What would be helpful now is a few examples of type `Countable`. The simplest countable
"thing" is just a natural number. To convert a natural number into a natural number,
it's safe to just use `id`:

> ex5 = wrap (Ind nat) (n 5) (App id_ (Ind nat))

Another "thing" that can be counted is \\(\\text{Either} \\ \\mathbb{N} \\ \\mathbb{N}\\).
Our earlier `unwrapEither` function would be an excellent candidate for `f`: it would
pull out a single natural number from the sum type. Here's the corresponding `Countable`
instance:

> ex6 = wrap (apps (Ind either_) [Ind nat, Ind nat]) (inl (Ind nat) (Ind nat) (n 7)) (App unwrapEither (Ind nat))

Despite containing values of different types, our last two expressions have the same type: they're
both `Countable`. We can feed them into `count` without providing any additional type parameters:

> ex7 = App count ex5
> ex8 = App count ex6

This is effectively an abstract data type - we have a value that has only
one operation (that we can count on): coutning.

Let's also write some examples of actual modules in our language. We can, for
instance, re-use the module for natural numbers we defined earlier.

> natMod = Module (MkSymbol ["Nat", "Data"])
>     $ Map.fromList [("ℕ", Definition Public $ Left nat), ("pred", Definition Public $ Right (Function "pred" 1 (Prod (Ind nat) (Ind nat)) pred_))]
