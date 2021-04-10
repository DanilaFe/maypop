Here, I'll define what a Maypop "term" is.

{{< todo >}}Let's use LaTeX for types and kinds and so on.{{< /todo >}}
{{< todo >}}Let's be more clear about universe / type / etc{{< /todo >}}
{{< todo >}}Extract the common typeclasses into a single class?{{< /todo >}}

> {-# LANGUAGE FlexibleContexts #-}
> module Language.Maypop.Syntax where
> import Control.Monad.Reader
> import Control.Monad.Except

We'll be using DeBrujin indices, so there will be no strings (and thus,
no need to perform any complicated alpha renaming). We have the following
terms in the language:

* **A reference to a variable**. The integer argument in the argument is a DeBrujin index.
* **A lambda abstraction**. There's no need to provide a variable name for this abstraction (once again, because of DeBrujin indexing), but we _do_ need to provide a type for the argument. Thus, the first term is the type, and the second term is the body of the lambda.
* **An application**. There's not much more to say here.
* **A dependent product**, which is a generalization of a function type. Once again, there's no need to define a variable, but there _is_ a need to provide the input an output type.

> data Term
>     = Ref Int
>     | Abs Term Term
>     | App Term Term
>     | Prod Term Term
>     | Universe Universe

For convenience, we combine the references to the various
universes (__Prop__ and __Type(n)__) into a data type,
`Universe`:

> data Universe = Prop | Type Int

Let's work on type inference a little. First, a little
utility function to compute the type of a type. This
is straight out of the paper on the Calculus of Inductive Constructions.
{{< sidenote "right" "prop-set-note" "Prop" >}}
I was wondering why we have two "bottom-level" types (one for propositions,
and one for regular data). It turns out that only propositions can refer
to themselves, or else the system is no longer consistent.
{{< /sidenote >}} has the type __Type(0)__, and
each type __Type(n)__ has type __Type(n+1)__.

> nextUniverse :: Universe -> Universe
> nextUniverse Prop = Type 0
> nextUniverse (Type i) = Type $ i+1

And now, type inference. This can fail, so let's define
a type for type errors.

> data TypeError = FreeVariable Int | NotUniverse

Finally, on to the type inference function. We use the `MonadReader`
typeclass to require read-only access to the local environment \\(\\Gamma\\).

> infer :: (MonadReader [Term] m, MonadError TypeError m) => Term -> m Term
> infer (Ref n) = nth n <$> ask >>= maybe (throwError (FreeVariable n)) return
> infer (Abs t b) = Prod t <$> extend t (infer b) -- TODO we can use extend' here
> infer (App _ _) = undefined
> infer (Prod a b) = extend' a $ \ua -> inferU b >>= \ub -> return $ Universe $
>     case ub of
>         Prop -> Prop
>         t -> joinU ua t
> infer (Universe u) = return $ Universe $ nextUniverse u

The type of a term is yet another term. However, not all terms consitute valid types.
For instance, a lambda function is _not_ a type. Indeed, computation aside,
only the `Universe` constructor corresponds to a valid type. We'll leave evaluation
to a different function, and define a way to "cast" a term into a valid univere.

> intoUniverse :: MonadError TypeError m => Term -> m Universe
> intoUniverse (Universe u) = return u
> intoUniverse _ = throwError NotUniverse

We can use this to define a "stronger" version of `infer`:

> inferU :: (MonadReader [Term] m, MonadError TypeError m) => Term -> m Universe
> inferU t = infer t >>= intoUniverse

There are a few utility functions in the above definitions; let's take a look
at all of them in turn. First up is `nth`. It so happens that we need to safely access
the nth element in our environment (which is just a stack) -- this is equivalent
to looking up a variable name in a map. We do this in the most straightforward
way imaginable:

> nth :: Int -> [a] -> Maybe a
> nth _ [] = Nothing
> nth 0 (x:xs) = Just x
> nth n (x:xs) = nth (n-1) xs

Next, we have to be careful about the rules of the Calculus of Constructions. We
can't _just_ put a type straight from a lambda into the environment; it so happens
that out types can be ill-formed! Thus, we need to first verify
the well-formedness of our argument type (for that, it must be well formed _and_ a universe). 
Thus, extending the environment looks like the following:

> extend :: (MonadReader [Term] m, MonadError TypeError m) => Term -> m Term -> m Term
> extend t m = extend' t $ const m
>
> extend' :: (MonadReader [Term] m, MonadError TypeError m) => Term -> (Universe -> m Term) -> m Term
> extend' t f = inferU t >>= \u -> local (t:) (f u)

Next up, a `joinU` function. We have cumulativity, and one of the rules for product
types requires both input types \\(A\\) and \\(B\\) to be of the same sort __Type(i)__. This
need not be the case out of the box; however, types in CoC are a join semilattice, and
we can use our "join" function (aka "max") to find the supremum.

> joinU :: Universe -> Universe -> Universe
> joinU Prop Prop = Prop
> joinU (Type i) (Type j) = Type $ max i j
> joinU (Type i) _ = Type i
> joinU _ (Type i) = Type i
