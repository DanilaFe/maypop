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

Having the data type by itself is quite boring.
There are a few helpful functions we can implement on terms.
One of these function is the classic substitution, which
is crucial in beta reduction. If we were to use strings for our
terms, this would get fairly hairy. We'd need to perform alpha
renaming, keep tracking of shadowing, and do all sorts of
other things. However, DeBrujin indices make this
fairly easy. All we have to do is keep track of what number refers to
the variable we're substituting. When we enter the body of an abstraction,
another variable gets the index 0, so every reference is "shifted" by one.
Concretely, if we were replacing a variable `n` with a term outside an
abstraction, inside the abstraction `n+1` refers to that same variable.
We keep track of it accordingly.

> substitute :: Int -> Term -> Term -> Term
> substitute n t = sub 0
>     where
>         sub x (Ref m) | (n+x) == m = offsetFree x t
>         sub x (Abs t1 t2) = Abs (sub x t1) (sub (x+1) t2)
>         sub x (App t1 t2) = App (sub x t1) (sub x t2)
>         sub x (Prod t1 t2) = Prod (sub x t1) (sub (x+1) t2)
>         sub x t = t

It is perhaps surprising to see the use of `offsetFree` here. Why do we need to do anything
special while substituting? We don't if `t` is a closed term (that is, if it doesn't have free
variables). However, if it _does_ have free variables, we need to be careful to make sure that
these variables are pointing to the same spot. The (0-indexed) term \\(\\lambda.1\\) refers
to some free variable "outside", but if we substitute it into the body of another abstraction,
getting \\(\\lambda.\\lambda.1\\), it now refers to the first argument of the function.
This isn't what we want - a free variable reference in this term can't possibly refer to a
variable that only exists inside _another_ lambda abstraction. It's easy to see that,
to preserve free variables, we need to increment the free variables in the term being
substituted by the number of surrounding lambda abstractions in the destination. To
do so, we can define a function that increments (or decrements)
the free varibles in a given expression. We once again use a Reader monad
to keep track of the current number of surrounding lambda abstractions.

> offsetFree :: Int -> Term -> Term
> offsetFree o t = runReader (off t) 0
>     where
>         off (Ref i) = bool (Ref i) (Ref (i+o)) <$> asks (i>=)
>         off (Abs t1 t2) = liftA2 Abs (off t1) (deepen $ off t2)
>         off (App t1 t2) = liftA2 App (off t1) (off t2)
>         off (Prod t1 t2) = liftA2 Prod (off t1) (deepen $ off t2)
>         off t = return t
>         deepen m = local (+1) m

Another couple of helpful functions is `freeVars` and `occurs`. We'll use the latter
in our pretty printer: after all, the function arrow \\(A\\rightarrow B\\) is
a special case of the product type \\(\\Pi (a:A), B\\) where \\(a \\not\\in \\text{free}(B)\\).
Finding free variables is easy enough: at any subexpression, any DeBrujin index that's
greater than the number of surrounding abstractions or products is a free variable.
We use a Reader monad to keep track of the current number of surrounding abstractions.

> freeVars :: Term -> [Int]
> freeVars t = Set.toList $ runReader (freeVars' t) 0
>     where
>         freeVars' (Ref i) = bool Set.empty (Set.singleton i) <$> asks (i>=) 
>         freeVars' (Abs t1 t2) = liftA2 (<>) (freeVars' t1) (deepen $ freeVars' t2)
>         freeVars' (App t1 t2) = liftA2 (<>) (freeVars' t1) (freeVars' t2)
>         freeVars' (Prod t1 t2) = liftA2 (<>) (freeVars' t1) (deepen $ freeVars' t2)
>         freeVars' _ = return Set.empty
>         deepen m = (Set.map $ subtract 1) <$> local (+1) m

Since `freeVars` finds _all_ free variables in a term, checking if a single variable
occurs free becomes as simple as looking inside that list.

> occurs :: Int -> Term -> Bool
> occurs i = elem i . freeVars

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

Now we have all the machinery in place for wrangling our infinite
list of varaible names. We'll be using a State monad to keep track
of which names we have and haven't used. We can thus write a convenient
operation to generate a fresh name in such a context. This operation
generates a new name (by peeking at the infinite list of names via `headN`)
and then removes it from the list (by setting the name list to its tail via `tailN`).

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

In the above, we used a function `nth`. This is just a safe version of the `(!!)` operator
that is built into Haskell. It'll come in handy in other modules, too.

> nth :: Int -> [a] -> Maybe a
> nth _ [] = Nothing
> nth 0 (x:xs) = Just x
> nth n (x:xs) = nth (n-1) xs
