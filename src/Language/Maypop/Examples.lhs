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
> inl :: Term -> Term
> inl = App (Constr either_ 0)
>
> inr :: Term -> Term
> inr = App (Constr either_ 1)

Let's do a little bit of pattern matcing, shall we?

> ex1 :: Term
> ex1 = Case (n 3) nat (Ind nat) [n 0, Ref 0]
>
> ex2 :: Term
> ex2 = Abs (Ind nat) $ Abs (App (Ind fin) $ s (Ref 0)) $ Case (Ref 0) fin (App (Ind fin) (Ref 3)) [fz (Ref 2), Ref 0]
>
> ex3 :: Term
> ex3 = Case (inr $ n 0) either_ (Ind nat) []
