In this module, we'll use the syntax definitions from the `Syntax` module to
define a few example terms. This should make it more convenient to ensure
that the code is still operating as expected.

> module Language.Maypop.Examples where
> import Language.Maypop.Syntax

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

Let's also define an either data type.

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
>
> inl :: Term -> Term -> Term -> Term
> inl t1 t2 a = foldl App (Constr either_ 0) [t1, t2, a]
>
> inr :: Term -> Term -> Term -> Term
> inr t1 t2 a = foldl App (Constr either_ 1) [t1, t2, a]

And a pair data type.

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
>
> mkPair :: Term -> Term -> Term -> Term -> Term
> mkPair t1 t2 v1 v2 = foldl App (Constr pair_ 0) [t1,t2,v1,v2]

Let's do a little bit of pattern matcing, shall we?

> ex1 :: Term
> ex1 = Case (n 3) nat (Ind nat) [n 0, Ref 0]
>
> ex2 :: Term
> ex2 = Abs (Ind nat) $ Abs (App (Ind fin) $ s $ s (Ref 0)) $ Case (Ref 0) fin (App (Ind fin) $ s (Ref 3)) [fz (Ref 2)] -- FS case doesn't work
>
> ex3 :: Term
> ex3 = Abs (t 0) $ Abs (App (App (Ind either_) (Ref 0)) (Ref 0)) $ Case (Ref 0) either_ (Ref 2) [Ref 0, Ref 0]
>
> ex4 :: Term
> ex4 = Abs (t 0) $ Abs (t 0) $ Abs (App (App (Ind pair_) (Ref 1)) (Ref 0)) $ Case (Ref 0) pair_ (App (App (Ind pair_) (Ref 2)) (Ref 3)) [ mkPair (Ref 3) (Ref 4) (Ref 0) (Ref 1) ]
>
> ex5 :: Term
> ex5 = App (App ex3 (Ind nat)) $ inl (Ind nat) (Ind nat) $ n 3
>
> ex6 :: Term
> ex6 = App (App (App ex4 (Ind nat)) (Ind nat)) $ mkPair (Ind nat) (Ind nat) (n 3) (n 6)
