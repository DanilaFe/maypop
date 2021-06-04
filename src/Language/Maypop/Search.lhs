In this module, we'll implement a way to search for defined
type class instances, without having to manually provide
them.

> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE GeneralizedNewtypeDeriving #-}
> {-# LANGUAGE MonoLocalBinds #-}
> module Language.Maypop.Search where
> import Language.Maypop.Syntax
> import Language.Maypop.Checking
> import Language.Maypop.Unification
> import Language.Maypop.InfiniteList
> import Language.Maypop.Modules
> import Control.Applicative
> import Control.Monad
> import Control.Monad.Reader
> import Control.Monad.Identity
> import Control.Monad.Writer
> import Control.Monad.State
> import Control.Monad.Logic
> import Control.Monad.Except
> import qualified Data.Map as Map
> import Data.Foldable
> import Data.Void
> import Data.Maybe

The first thing that we will do is define a fresh kind of
parameter (for type safety). This will be a straightforward
wrapper around `String` using `newtype`, so that conversions
are easy, but explicit (and thus, it's harder to write incorrect code).

> newtype Meta = MkMeta { unMeta :: String } deriving (Eq, Ord, Show, Infinite)

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

{{< todo >}}Explain all this.{{< /todo >}}

> data RecipeParam a = Meta a | Search (ParamTerm a) deriving Show
> 
> data Recipe a = Recipe
>     { rParams :: [RecipeParam a]
>     , rConclusion :: ParamTerm a
>     , rFunc :: Function
>     } deriving Show
>
> validate :: MonadError TypeError m => ParamTerm (Either () Meta) -> m (ParamTerm Meta)
> validate = traverse (either (const (throwError TypeError)) return)
>
> intoMeta :: MonadError TypeError m => [ParamTerm (Either () Meta)] -> Term -> m (ParamTerm Meta)
> intoMeta ps t = validate $ substituteMany 0 (reverse ps) (parameterize t)
>
> walkProd :: (MonadInfer Void m, MonadState (InfList Meta) m, MonadWriter [RecipeParam Meta] m) => [ParamTerm (Either () Meta)] -> Term -> m (ParamTerm Meta)
> walkProd ps (Prod l r) = do
>     lt <- infer l
>     p <- case lt of
>         Sort Constraint -> do
>            lm' <- intoMeta ps l
>            tell [Search lm']
>            return $ Param $ Left ()
>         _ -> do
>            mv <- gets headInf <* modify tailInf
>            tell [Meta mv]   
>            return $ Param $ Right mv
>     extend l $ walkProd (p:ps) r
> walkProd ps t = do
>     tt <- infer t
>     case tt of
>         Sort Constraint -> intoMeta ps t
>         _ -> mzero
>
> intoRecipe :: Function -> Maybe (Recipe Meta)
> intoRecipe f = either (const Nothing) makeRecipe mResult
>     where
>         mResult = runInferE [] (runStateT (runWriterT (walkProd [] $ fFullType f)) infList)
>         makeRecipe ((c, ps), _) = Just $ Recipe ps c f
>
> intoRecipies :: GlobalScope -> [Recipe Meta]
> intoRecipies = catMaybes . map (into . eVariant) . Map.elems . sQualified
>     where
>         into (FunExport f) = intoRecipe f
>         into _ = Nothing
>
> newVar :: (Ord mv, MonadUnify k v m, MonadState (Map.Map mv k) m) => mv -> m k
> newVar m = do { v <- fresh; modify (Map.insert m v); return v }
>
> getVar :: (Ord mv, MonadUnify k v m, MonadState (Map.Map mv k) m) => mv -> m k
> getVar mv = gets (Map.lookup mv) >>= maybe (newVar mv) return
>
> instantiate :: MonadUnify k (ParamTerm k) m => Recipe Meta -> m (Recipe k)
> instantiate r = fst <$> runStateT (liftA3 Recipe rParams' rConclusion' (pure $ rFunc r)) Map.empty
>     where
>         rParams' = mapM instParam (rParams r)
>         rConclusion' = instTerm (rConclusion r)
>         instTerm = traverse getVar
>         instParam (Meta a) = Meta <$> getVar a
>         instParam (Search t) = Search <$> instTerm t
>
> data SearchError = NoSolutions | Overlapping | Ambiguous deriving Show
>
> runSearch :: [Recipe Meta] -> Term -> Either SearchError Term
> runSearch ps t = validateSearch $ runIdentity $ observeAllT (runReaderT (runUnifyT doSearch) ps)
>     where doSearch = search (parameterize t) >>= reify
>
> validateSearch :: [ParamTerm String] -> Either SearchError Term
> validateSearch [] = throwError NoSolutions
> validateSearch [t] = maybe (throwError Ambiguous) return $ strip t
> validateSearch _ = throwError Overlapping
>
> search :: (MonadLogic m, MonadUnify k (ParamTerm k) m, MonadReader [Recipe Meta] m) => ParamTerm k -> m (ParamTerm k)
> search t = ask >>= asum . map (recipe t)
>
> recipe :: (MonadLogic m, MonadUnify k (ParamTerm k) m, MonadReader [Recipe Meta] m) => ParamTerm k -> Recipe Meta -> m (ParamTerm k)
> recipe t r =
>     do
>         ir <- instantiate r
>         unify t (rConclusion ir)
>         params <- mapM findParam (rParams ir)
>         return $ foldl App (Fun $ rFunc r) params
>     where
>         findParam (Meta a) = return (Param a)
>         findParam (Search t) = search t
