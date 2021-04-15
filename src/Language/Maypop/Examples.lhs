In this module, we'll use the syntax definitions from the `Syntax` module to
define a few example terms. This should make it more convenient to ensure
that the code is still operating as expected.

> module Language.Maypop.Examples where
> import Language.Maypop.Syntax

For convenience, we'll use `p` to referm to the term `Prop`, and `t n` to refer
to the term `Universe (Type n)`.

> p = Universe Prop
> t = Universe . Type

In the absense of concrete types, the simplest term I can think of is the polymorphic
identity function. This function takes its argument type as input first, then an argument
of that type, and returns the argument unchanged.

> id_ :: Term
> id_ = Abs (t 0) $ Abs (Ref 0) $ Ref 0

In a similar vein, we can define Haskell's `const` function. Much like the identity function,
it does not require any other data types, and does not need to look into its arguments.

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

Why don't we define some data types? Here's one for natural numbers.

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

And here's one for bounded natural numbers.

> fin :: Inductive
> fin = Inductive
>     { iParams = []
>     , iArity = [ Ind nat ]
>     , iSort = Type 0
>     , iName = "Fin"
>     , iConstructors =
>         [ Constructor { cParams = [ Ind nat ], cIndices = [ Ref 0 ], cName = "FZ" }
>         , Constructor { cParams = [ Ind nat, App (Ind fin) (Ref 0) ], cIndices = [ App (Constr nat 1) (Ref 1) ], cName = "FS" }
>         ]
>     }
>
> fz :: Int -> Term
> fz m = App (Constr fin 0) (n m)
> 
> fs :: Int -> Term -> Term
> fs m = App (App (Constr fin 1) (n m))
