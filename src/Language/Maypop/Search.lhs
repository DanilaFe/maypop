In this module, we'll implement a way to search for defined
type class instances, without having to manually provide
them.

> {-# LANGUAGE FlexibleContexts #-}
> module Language.Maypop.Search where
> import Language.Maypop.Syntax
> import Language.Maypop.Unification
> import Language.Maypop.InfiniteList
> import Language.Maypop.Modules
> import Control.Applicative
> import Control.Monad
> import Control.Monad.State
> import qualified Data.Map as Map

The first thing that we will do is define a fresh kind of
parameter (for type safety). This will be a straightforward
wrapper around `String` using `newtype`, so that conversions
are easy, but explicit (and thus, it's harder to write incorrect code).

> newtype Meta = MkMeta { unMeta :: String } deriving (Eq, Ord, Show)

We will call this type `Meta` because we will attempt to interpret
functions returning values of kind `Constraint` as being
[rule schemas with metavariables](https://en.wikipedia.org/wiki/Rule_of_inference).
For example, consider the following function that produces an instance of
`Show (Vec A n)` (a vector of elements of type `A` having the length `n`):

```
showVec : forall (n : Nat). forall (A : Type 0). Show A -> Show (Vec A n)
```

We will treat the non-`Constraint` parameters (of types `Nat` and `Type 0`,
which themselves have types `Type 0` and `Type 1`, respectively) as
metavariables, and the `Constraint` parameter (`Show A` in this case)
as the premise of our inference rule. The result of the function will,
of course, be our conclusion. The "mathematical" interpretation of the
above rule would thus be:

\$$
\\texttt{SV}
\\frac
    {\\text{Show}\\ a}
    {\\text{Show} \\ (\\text{Vec} \\ a \\ n)}
\$$

For another example, take a look at this function producing a `Show` instance
for pair data type `Pair A B`:

```
showPair : forall (A B : Type 0). Show A -> Show B -> Show (Pair A B)
```

Once again, `A` and `B` have type `Type 0`, which itself has type `Type 1`;
We thus treat them as metavariables. However, `Show A` and `Show B`
both have type `Constraint`, and are therefore made into premises:

\$$
\\texttt{SP}
\\frac
    {\\text{Show}\\ a \\quad \\text{Show}\\ b}
    {\\text{Show} \\ (\\text{Pair} \\ b \\ a)}
\$$

Now, can we determine the `Show` instance for `Vec (Pair Nat Bool) 3`?
We can; it will require an instance of both of the above rules, as well
as the assumption that we can `Show` natural numbers and booleans. The proof
tree would be as follows:

\$$
\\texttt{SV}\\frac
    {
        \\texttt{SP}\\cfrac
            {\\text{Show}\\ \\mathbb{N} \\quad \\text{Show}\\ \\mathbb{B}}
            {\\text{Show} \\ (\\text{Pair}\\ \\mathbb{N}\\ \\mathbb{B})}
    }
    {\\text{Show} \\ (\\text{Vec} \\ (\\text{Pair}\\ \\mathbb{N}\\ \\mathbb{B})\\ 3)}
\$$

In the above tree, we instantiated `showVec` (\\(\\texttt{SV}\\) in the mathematical notation)
with \\(a = \\text{Pair}\\ \\mathbb{N}\\ \\mathbb{B}\\) and \\(n = 3\\).
We also instantiated `showPair` with \\(a = \\mathbb{N}\\) and \\(b = \\mathbb{B}\\).
Importantly, notice that these are two different \\(a\\)s! The metavariables
are local to their particular instance of an inference rule. To further drive
home this point, consider the below proof tree for the `Show` instance of
`Pair (Pair Nat Bool) Nat`:

\$$
\\texttt{SP}\\frac
    {
        \\texttt{SP}\\cfrac
            {\\text{Show}\\ \\mathbb{N} \\quad \\text{Show}\\ \\mathbb{B}}
            {\\text{Show} \\ (\\text{Pair}\\ \\mathbb{N}\\ \\mathbb{B})}
        \\quad
        \\text{Show}\\ \\mathbb{N}
    }
    {\\text{Show} \\ (\\text{Pair} \\ (\\text{Pair}\\ \\mathbb{N}\\ \\mathbb{B})\\ \\mathbb{N})}
\$$

Here, we instantiated `showPair` twice, once with \\(a = \\text{Pair}\\ \\mathbb{N}\\ \\mathbb{B}\\) and \\(b = \\mathbb{N}\\),
and once more with \\(a = \\mathbb{N}\\) and \\(b = \\mathbb{B}\\). Once again, even though we're using
the same rule _schema_ (`showPair`/\\(\\texttt{SP}\\)), we are using it with different variable
bindings!

Let's get back to some Haskell code. First of all, we clearly have a variant of terms that
contain metavariables as parameters. We can define a type alias for this variant:

> type MetaExpr = ParamTerm Meta

{{< todo >}}Explain all this.{{< /todo >}}

> data Rule a = Rule
>     { rPremises :: [ParamTerm a]
>     , rConclusion :: ParamTerm a
>     }
>
> type MetaRule = Rule Meta
>
> instantiate :: MonadUnify k (ParamTerm k) m => MetaRule -> m (Rule k)
> instantiate mr = fst <$> runStateT (liftA2 Rule (mapM inst $ rPremises mr) (inst $ rConclusion mr)) Map.empty
>     where
>         newVar m = do
>             v <- fresh
>             modify (Map.insert m v)
>             return v
>         getVar m = gets (Map.lookup m) >>= maybe (newVar m) return
>         inst = traverse getVar
