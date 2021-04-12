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
