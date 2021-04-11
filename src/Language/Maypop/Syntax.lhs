Here, I'll define what a Maypop "term" is.

{{< todo >}}Let's use LaTeX for types and kinds and so on.{{< /todo >}}
{{< todo >}}Let's be more clear about universe / type / etc{{< /todo >}}
{{< todo >}}Extract the common typeclasses into a single class?{{< /todo >}}
{{< todo >}}Increment variable references for free variables in substitution.{{< /todo >}}
{{< todo >}}Move the explanation for nth earlier up.{{< /todo >}}

> {-# LANGUAGE FlexibleContexts #-}
> module Language.Maypop.Syntax where
> import Control.Applicative
> import Control.Monad.Reader
> import Control.Monad.Except
> import Control.Monad.State
> import Data.Bool
> import qualified Data.Set as Set

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
>     deriving Eq

For convenience, we combine the references to the various
universes (__Prop__ and __Type(n)__) into a data type,
`Universe`:

> data Universe = Prop | Type Int deriving (Eq, Show)

There are a few helpful functions we can implement on terms.
One of these function is the classic substitution, which
is crucial in beta reduction. DeBrujin indices make this
fairly easy; we need not keep track of names or alpha renaming.
All we have to do is keep track of what number refers to
the variable we're substituting. This is done by incrementing
the target number at abstractions and products (since they introduce
their own bindings, and therefore shift the indices).

> substitute :: Int -> Term -> Term -> Term
> substitute n t (Ref m) | n == m = t
> substitute n t (Abs t1 t2) = Abs (substitute n t t1) (substitute (n+1) t t2)
> substitute n t (App t1 t2) = App (substitute n t t1) (substitute n t t2)
> substitute n t (Prod t1 t2) = Prod (substitute n t t1) (substitute (n+1) t t2)
> substitute _ _ t = t

Another couple of helpful functions is `freeVars` and `occurs`. We'll use the latter
in our pretty printer: after all, the function arrow \\(A\\rightarrow B\\) is
a special case of the product type \\(\\Pi (a:A), B\\) where \\(a \\not\\in \\text{free}(B)\\).
Finding free variables is easy enough: at any subexpression, any DeBrujin index that's
greater than the number of surrounding abstractions or products is a free variable.

> freeVars :: Term -> [Int]
> freeVars t = Set.toList $ runReader (freeVars' t) 0
>     where
>         freeVars' (Ref i) = bool Set.empty (Set.singleton i) <$> asks (i>=) 
>         freeVars' (Abs t1 t2) = liftA2 (<>) (freeVars' t1) (deepen $ freeVars' t2)
>         freeVars' (App t1 t2) = liftA2 (<>) (freeVars' t1) (freeVars' t2)
>         freeVars' (Prod t1 t2) = liftA2 (<>) (freeVars' t1) (deepen $ freeVars' t2)
>         freeVars' _ = return Set.empty
>         deepen m = (Set.map $ subtract 1) <$> local (+1) m
> 
> occurs :: Int -> Term -> Bool
> occurs i = elem i . freeVars

We can define a function that increments (or decrements)
the free varibles in a given expression. This is useful for a variety of things, but
most notably beta reduction: when we eliminate a lambda abstraction, the indices representing
free variables need to be changed to ensure they're still pointing in the same spot.
This leads to the following definition:

> offsetFree :: Int -> Term -> Term
> offsetFree o t = runReader (off t) 0
>     where
>         off (Ref i) = bool (Ref i) (Ref (i+o)) <$> asks (i>=)
>         off (Abs t1 t2) = liftA2 Abs (off t1) (deepen $ off t2)
>         off (App t1 t2) = liftA2 App (off t1) (off t2)
>         off (Prod t1 t2) = liftA2 Prod (off t1) (deepen $ off t2)
>         off t = return t
>         deepen m = local (+1) m

How about a pretty printer? Our language is simple enough. To make our expressions
more readable to humans, we will use an infinite list of variable names, and
assign to each abstraction a fresh name. It's conventional to distinguish different
types of variables (plain variables, type variables) by using a different alphabet,
but this requires typechecking, and that's a lot more work than I think a pretty printer
should do. Thus, we'll just use a simple, infinite, homogenous list of names. We can
define it as follows:

> data Names = Cons String Names

It's nice to be able to construct (the beginning of) an infinite list
from a "regular" list. That's easy enough:

> fromList :: [String] -> Names -> Names
> fromList xs ns = foldr Cons ns xs

We also want to be able to transform a single element of this list
into many elements (we use this to build up longer and longer names
as we run out of short ones).

> expand :: (String -> [String]) -> Names -> Names
> expand f (Cons x xs) = fromList (f x) (expand f xs)

Finally, we define an infinite list of names, which first consists
of all single-letter names, and then all two letter names (alphabetically ordered),
and so on.

> names :: Names
> names = fromList (map return alphabet) $ expand (\s -> ((s++) . return) <$> alphabet) names
>     where alphabet = ['a'..'z']

Finally, we need ways to get the current head (next string) and the current tail (the rest of the names).
Unlike those for list, these functions are guaranteed to be safe, since we can never exhaust our
infinite list.

> headN :: Names -> String
> headN (Cons x _) = x
>
> tailN :: Names -> Names
> tailN (Cons _ xs) = xs

Next, a convenience function. Assuming we have a State monad
whose content is the infinite list of names, this will return
the current name _and_ modify the state to no longer include
that name.

> popName :: MonadState Names m => m String
> popName = gets headN <* modify tailN

And now, the pretty printer itself.

> instance Show Term where
>     show t = fst $ runState (runReaderT (showM t) []) names
>         where
>             showM (Ref i) = nth i <$> ask >>= maybe (return "??") return
>             showM (Abs t1 t2) = do
>                 newName <- popName
>                 st1 <- showM t1
>                 st2 <- local (newName:) $ showM t2
>                 return $ "λ(" ++ newName ++ ":" ++ st1 ++ ")." ++ st2
>             showM (App t1 t2) =
>                 liftA2 (\s1 s2 -> s1 ++ "(" ++ s2 ++ ")") (showM t1) (showM t2)
>             showM (Prod t1 t2) = do
>                 newName <- popName
>                 st1 <- showM t1
>                 st2 <- local (newName:) $ showM t2
>                 if occurs 0 t2
>                  then return $ "∀(" ++ newName ++ ":" ++ st1 ++ ")." ++ st2
>                  else return $ "(" ++ st1 ++ ") → " ++ st2
>             showM (Universe u) = return $ show u

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

> data TypeError = FreeVariable Int | NotUniverse | NotProduct | TypeError deriving Show

Finally, on to the type inference function. We use the `MonadReader`
typeclass to require read-only access to the local environment \\(\\Gamma\\).

> infer :: (MonadReader [Term] m, MonadError TypeError m) => Term -> m Term
> infer (Ref n) = nth n <$> ask >>= maybe (throwError (FreeVariable n)) return
> infer (Abs t b) = Prod t <$> extend t (infer b) -- TODO we can use extend' here
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
at all of them in turn.  First up is `inferU`. The type of a term is yet another term.
However, not all terms consitute valid types. For instance, a lambda function is _not_ a
type. Indeed, computation aside, only the `Universe` constructor corresponds to a valid
type. We'll leave evaluation to a different function, and define a way to "cast" a term
into a valid univere.

> intoUniverse :: MonadError TypeError m => Term -> m Universe
> intoUniverse (Universe u) = return u
> intoUniverse _ = throwError NotUniverse

We can use this to define a "stronger" version of `infer`:

> inferU :: (MonadReader [Term] m, MonadError TypeError m) => Term -> m Universe
> inferU t = infer t >>= intoUniverse

A similar casting function to `intoUniverse` is `intoProduct`, which helps
us required that a term is a dependent product (this is used for the application rule).
Once again, we do not concern ourselves with evaluation. Finally, we return the
two terms composing a product type rather than returning a `Term`.

> intoProduct :: MonadError TypeError m => Term -> m (Term, Term)
> intoProduct (Prod a b) = return (a, b)
> intoProduct _ = throwError NotProduct
> 
> inferP :: (MonadReader [Term] m, MonadError TypeError m) => Term -> m (Term, Term)
> inferP t = infer t >>= intoProduct

Next up up is `nth`. It so happens that we need to safely access
the nth element in our environment (which is just a stack) -- this is equivalent
to looking up a variable name in a map. We do this in the most straightforward
way imaginable:

> nth :: Int -> [a] -> Maybe a
> nth _ [] = Nothing
> nth 0 (x:xs) = Just x
> nth n (x:xs) = nth (n-1) xs

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

Next up, a `joinU` function. We have cumulativity, and one of the rules for product
types requires both input types \\(A\\) and \\(B\\) to be of the same sort __Type(i)__. This
need not be the case out of the box; however, types in CoC are a join semilattice, and
we can use our "join" function (aka "max") to find the supremum.

> joinU :: Universe -> Universe -> Universe
> joinU Prop Prop = Prop
> joinU (Type i) (Type j) = Type $ max i j
> joinU (Type i) _ = Type i
> joinU _ (Type i) = Type i
