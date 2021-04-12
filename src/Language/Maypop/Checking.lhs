Let's work on type inference a little.

> {-# LANGUAGE FlexibleContexts #-}
> module Language.Maypop.Checking where
> import Language.Maypop.Syntax
> import Control.Applicative
> import Control.Monad.Reader
> import Control.Monad.Except
> import Control.Monad.State

First, a little utility function to compute the type of a type. This
is straight out of the paper on the Calculus of Inductive Constructions.
Prop has the type __Type(0)__, and each type __Type(n)__ has type __Type(n+1)__.

> nextUniverse :: Universe -> Universe
> nextUniverse Prop = Type 0
> nextUniverse (Type i) = Type $ i+1

Type inference can fail, so let's define a type for any kind of error that can
come up.

> data TypeError = FreeVariable Int | NotUniverse | NotProduct | TypeError deriving Show

Finally, on to the type inference function. We use the `MonadReader`
typeclass to require read-only access to the local environment \\(\\Gamma\\).

> infer :: (MonadReader [Term] m, MonadError TypeError m) => Term -> m Term
> infer (Ref n) = nth n <$> ask >>= maybe (throwError (FreeVariable n)) return
> infer (Abs t b) = Prod t <$> extend t (infer b)
> infer (App f a) = do
>     (ta, tb) <- inferP f
>     targ <- infer a
>     if ta == targ
>      then return (substitute 0 a tb)
>      else throwError TypeError
> infer (Prod a b) = extend' a $ \ua -> inferU b >>= \ub -> return $ Universe $
>     case ub of
>         Prop -> Prop
>         t -> joinU ua t
> infer (Universe u) = return $ Universe $ nextUniverse u
>
> runInfer :: Term -> Either TypeError Term
> runInfer t = runReader (runExceptT $ infer t) []

There are a few utility functions in the above definitions; let's take a look
at all of them in turn.  First up is `inferU`. We need this function because
not all terms consitute valid types. For instance, a lambda function is _not_ a
type, but it is a term. Indeed, computation aside, only the `Universe` constructor corresponds
to a valid type. However, some constructs in the Calculus of Constructions specifically require types,
such as \\(\\Pi\\). Thus, we'll define a way to "cast" a term into a valid univere. This will
be used to discard terms such as \\(\\Pi(\\lambda \\textbf{Prop}.0),\\textbf{Prop}\\), which have non-types in a
place where a type is needed.

> intoUniverse :: MonadError TypeError m => Term -> m Universe
> intoUniverse (Universe u) = return u
> intoUniverse _ = throwError NotUniverse

We can use this to define a specialized version of `infer`:

> inferU :: (MonadReader [Term] m, MonadError TypeError m) => Term -> m Universe
> inferU t = infer t >>= intoUniverse

A similar casting function to `intoUniverse` is `intoProduct`, which helps
us require that a term is a dependent product (this is used for the application rule).
We return the two terms composing a product type rather than returning a `Term`, which
helps the type system "remember" that this is not just any term that passed our inspection.

> intoProduct :: MonadError TypeError m => Term -> m (Term, Term)
> intoProduct (Prod a b) = return (a, b)
> intoProduct _ = throwError NotProduct

Once again, we define a specailized version of `infer` for products:

> inferP :: (MonadReader [Term] m, MonadError TypeError m) => Term -> m (Term, Term)
> inferP t = infer t >>= intoProduct

Next, we have to be careful about the rules of the Calculus of Constructions. We
can't _just_ put a type straight from a lambda into the environment; it so happens
that our types can be ill-formed! Thus, we need to first verify
the well-formedness of our argument type (for that, it must be well formed _and_ a universe). 
Furthermore, because types in the environment can refer to terms via DeBrujin
indices, we must be careful to preserve these references inside the body of a lambda
abstraction, leading us to use `offsetFree`. Thus, extending the environment looks like this:

> extend :: (MonadReader [Term] m, MonadError TypeError m) => Term -> m Term -> m Term
> extend t m = extend' t $ const m
>
> extend' :: (MonadReader [Term] m, MonadError TypeError m) => Term -> (Universe -> m Term) -> m Term
> extend' t f = inferU t >>= \u -> local (map (offsetFree 1) . (t:)) (f u)

The Calculus of Constructions has cumulativity, and one of the rules for product
types requires both input types \\(A\\) and \\(B\\) to be of the same sort __Type(i)__. This
need not be the case out of the box; however, types in CoC are
{{< sidenote "right" "semilattice-note" "a join semilattice," >}}
In our implementation they're actually a total order. However, in languages like Coq,
there are "two" base types, Prop and Set. Thus, in the "real world", we don't have
a total order, but we do have a join semilattice.
{{< /sidenote >}} and we can use our "join" function (aka "max") to find the supremum.

> joinU :: Universe -> Universe -> Universe
> joinU Prop Prop = Prop
> joinU (Type i) (Type j) = Type $ max i j
> joinU (Type i) _ = Type i
> joinU _ (Type i) = Type i
