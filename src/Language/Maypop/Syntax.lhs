Here, I'll define what a Maypop "term" is.

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
universes (__Set__, __Prop__, and __Type(n)__) into a data type,
`Universe`:

> data Universe = Prop | Set | Type Int

Let's work on type inference a little. First, a little
utility function to compute the type of a type. This
is straight out of the paper on the Calculus of Inductive Constructions.
{{< sidenote "right" "prop-set-note" "Both Prop and Set" >}}
I was wondering why we have two "bottom-level" types (one for propositions,
and one for regular data). It turns out that only propositions can refer
to themselves, or else the system is no longer consistent.
{{< /sidenote >}} have the type __Type(0)__, and
each type __Type(n)__ has type __Type(n+1)__.

> nextUniverse :: Universe -> Universe
> nextUniverse Prop = Type 0
> nextUniverse Set = Type 0
> nextUniverse (Type i) = Type $ i+1

And now, type inference. This can fail, so let's define
a type for type errors.

> data TypeError = FreeVariable Int

It so happens that we need to safely access the nth element
in our environment (which is just a stack). For this, we
define a list access function:

> nth :: Int -> [a] -> Maybe a
> nth _ [] = Nothing
> nth 0 (x:xs) = Just x
> nth n (x:xs) = nth (n-1) xs

Finally, on to the type inference function. We use the `MonadReader`
typeclass to require read-only access to the local environment \\(\\Gamma\\).

> infer :: (MonadReader [Term] m, MonadError TypeError m) => Term -> m Term
> infer (Ref n) = nth n <$> ask >>= maybe (throwError (FreeVariable n)) return
> infer (Abs _ _) = undefined
> infer (App _ _) = undefined
> infer (Prod a b) = undefined
> infer (Universe u) = return $ Universe $ nextUniverse u
