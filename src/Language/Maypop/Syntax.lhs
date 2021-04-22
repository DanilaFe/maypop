Here, I'll define what a Maypop "term" is.

{{< todo >}}Let's use LaTeX for types and kinds and so on.{{< /todo >}}
{{< todo >}}Let's be more clear about universe / type / etc{{< /todo >}}
{{< todo >}}Extract the common typeclasses into a single class?{{< /todo >}}
{{< todo >}}Inductive stuff has names? How does equality work?{{< /todo >}}
{{< todo >}}Introduce binders.{{< /todo >}}

> {-# LANGUAGE FlexibleContexts #-}
> module Language.Maypop.Syntax where
> import Control.Applicative
> import Control.Monad.Reader
> import Control.Monad.Except
> import Control.Monad.State
> import Control.Monad.Writer
> import Data.Bool
> import Data.List
> import qualified Data.Set as Set
>

Before we get started on the terms of the Calculus of Inductive Constructions,
we need to talk about the "Inductive" part. We have inductive data types, more
specifically inductive GADTs in our language. Each inductive data type accepts
some parameters, an "arity" declaration, and constructors. In general, the
paper I'm using as reference defines the following form:

```
Inductive I (p1 : A1) ... (pn : An) : B1 -> ... -> Bm -> s where
    C : forall (x1 : C1) ... (xp : Cp) -> I p1 ... pn u1 ... um
    ...
```

There are a lot of parts to this definition, so let's take a look
at all of them in turn. First, we have _parameters_, `p1` through `pn`.
These are shared between all constructors of this data type. For instance,
in a polymorphic list, the type of the elements in the list may be a
parameter, and we'd write:

```
Inductive List (t : Type 0) : Type 0 where
    ...
```

We could then use `t` to refer to the type of elements in both the
`Cons` and `Nil` constructors.

Next up is the arity. Our inductive definition, in general, defines
a type family indexed by terms in our language. This declaration
lists the types of these indexing terms, `B1` through `Bm`. Each
constructor must specify the indexing terms of corresponding types.

Finally, we have constructors. Constructors can take more arguments
than have already been given via the parameters: the `Cons` constructor
of the above `List`, for instance, would accept two additional parameters, one
of type `t` and one of type `List t`. The `Nil` constructor, on the other hand,
would accept no additional parameters. Finally, each constructor must
return the type family defined by the data type, applied to the aforementioned
indexing terms.

We encode this in the following two inductive definitions. In our view,
a constructor must have its own parameters (`cParams`), the index terms
that it applies to the data type (`cIndices`), and it would be good
(for debugging at the very least) for it to have a name (`cName`).
An entire data type declaration must have its shared parameters
(`iParams`), it's arity (`iArity`, which we represent as just the
list of argument terms `B1` through `Bm`), the sort that it returns (`iSort`),
a list of its constructors (`iConstructors`) and, once again, a name (`iName`).

> data Constructor = Constructor
>     { cParams :: [Term]
>     , cIndices :: [Term]
>     , cName :: String
>     }
>
> data Inductive = Inductive
>     { iParams :: [Term]
>     , iArity :: [Term]
>     , iSort :: Universe
>     , iConstructors :: [Constructor]
>     , iName :: String
>     }

Equality on data types is required, but hard to provide. For now, We'll
just compare their names.

> instance Eq Inductive where
>     i1 == i2 = iName i1 == iName i2

Finally, it's time to describe the terms in our language.
We'll be using DeBrujin indices, so there will be
{{< sidenote "right" "no-strings-note" "no strings" >}}
Except for the names of inductive datatypes and their constructors,
but I hope to be able to eliminate this information in the final
version of the project.
{{< /sidenote >}}(and thus,
no need to perform any complicated alpha renaming). We have the following
terms in the language:

* **A reference to a variable**. The integer argument in the argument is a DeBrujin index.
* **A lambda abstraction**. There's no need to provide a variable name for this abstraction (once again, because of DeBrujin indexing), but we _do_ need to provide a type for the argument. Thus, the first term is the type, and the second term is the body of the lambda.
* **An application**. There's not much more to say here.
* **A dependent product**, which is a generalization of a function type. Once again, there's no need to define a variable, but there _is_ a need to provide the input an output type. Unlike a regular function, a dependent
product's output type can depend on the value, and not just the type, of the input.
* **A reference to a sort**, like \\(\\text{Prop}\\) or \\(\\text{Type}_0\\).
* **An inductive type constructor**, referring to an inductively-defined type discussed above. We refer to it
by a direct reference to the `Inductive` object to avoid having to resolve names.
* **A constructor of an inductively defined type**. Once again, to avoid having to resolve names,
we refer to a constructor by the inductive type it constructs, and the index into the list
of that type's constructors.
* **A case expression**. This works much like the case expression in Haskell, except
that the expected type of the term being case analyzed (and the result type of the expression)
must be explicitly specified. The `Inductive` argument
{{< sidenote "right" "inductive-arg-note" "defines the expected term type," >}}
The various indexing terms for the inductive type constructor are assigned
names (no additional code is required here since we are just using DeBrujin indexing).
These names are available only to the subsequent type expression.
{{< /sidenote >}}
the `Term` argument is the expression for the type, and `[Term]` is a list
of branches for each constructor (the first term in the list is the expression
for the second constructor).

> data Term
>     = Ref Int
>     | Abs Term Term
>     | App Term Term
>     | Prod Term Term
>     | Universe Universe
>     | Constr Inductive Int
>     | Ind Inductive
>     | Case Term Inductive Term [Term]
>     deriving Eq

For convenience, we combine the references to the various
universes (\\(\\text{Prop}\\) and \\(\\text{Type}_n\\)) into a data type,
`Universe`:

> data Universe = Prop | Type Int deriving (Eq, Show)

Having the term data type by itself is quite boring.
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

Before we get to that, a quick aside. There will be several operations
in our language in which we'll need to keep track of the number
of surrounding binders. When case expressions come into play,
there are even more cases (no pun intended) in which we need
to increment our "counter" of variables. Rather than repeatedly
implementing this functionality -- perhaps with slight changes --
it's better to write a generic operation that will help
us reuse some code. To achieve this, let's assume that the
number of surrounding binders -- either from lambda abstractions
or from pattern matching -- is kept inside of a `Reader` monad,
which we will represent with `MonadReader Int`. Then, we can
define a generic operation that transforms __only free variable terms__,
with other possible monadic effects captured by the arbitrary monad `m`:

> transform :: MonadReader Int m => (Int -> m Term) -> Term -> m Term
> transform f = trans
>     where
>         trans (Ref m) = ask >>= \x -> if m >= x then f m else return (Ref m)
>         trans (Abs t1 t2) = liftA2 Abs (trans t1) (deepen 1 $ trans t2)
>         trans (App t1 t2) = liftA2 App (trans t1) (trans t2)
>         trans (Prod t1 t2) = liftA2 Prod (trans t1) (deepen 1 $ trans t2)
>         trans (Case t i tt ts) = do
>             t' <- trans t
>             tt' <- deepen (length $ iArity i) $ trans tt
>             ts' <- zipWithM (deepen . length . cParams) (iConstructors i) (map trans ts)
>             return $ Case t' i tt' ts'
>         trans t = return t
>         deepen i = local (+i)

Substitution is a special case of this kind of transformation.
When encountering a free variable, it replaces it with the given term `t`.

> substitute :: Int -> Term -> Term -> Term
> substitute n t r = runReader (transform op r) 0
>     where op _ = ask >>= \x -> return $ offsetFree x t

It is perhaps surprising to see the use of `offsetFree` here. Why do we need to do anything
special while substituting? We don't if `t` is a closed term (that is, if it doesn't have free
variables). However, if it _does_ have free variables, we need to be careful to make sure that
these variables are pointing to the same spot. The (0-indexed) term \\(\\lambda.1\\) refers
to some free variable "outside", but if we substitute it into the body of another abstraction,
getting \\(\\lambda.\\lambda.1\\), it now refers to the first argument of the resulting binary function.
This isn't what we want - a free variable reference in this term can't possibly refer to a
variable that only exists inside _another_ lambda abstraction. It's easy to see that
to preserve free variables, we need to increment the free variables in the term being
substituted by the number of surrounding binders in the destination. To
do so, we can define a function that increments (or decrements)
the free varibles in a given expression. That's exactly what `offsetFree`
does. This function is also a special case of the above `transform` operation,
since it adds a constant number `o` to each free variable term it encounters.

> offsetFree :: Int -> Term -> Term
> offsetFree o t = runReader (transform op t) 0
>     where op i = return $ Ref $ i + o

Another couple of helpful functions is `freeVars` and `occurs`. We'll use the latter
in our pretty printer: after all, the function arrow \\(A\\rightarrow B\\) is
a special case of the product type \\(\\Pi (a:A), B\\) where \\(a \\not\\in \\text{free}(B)\\).
Given our transformation function, finding free variables is very easy. We can
take advantage of the polymorphic type of our monad, `m`, and require that it also
be a `Writer` monad, which carries around a piece of data we can write to, but never read.
In our case, this piece of data will be a set of free variables. Each time our transformation
operation will encounter a free variable, it will emit it (using `tell`), but leave
it intact (via `const (Ref i)`). When emitting, we need to be careful to subtract
the number of surrounding binders: \\(\\lambda.1\\) and \\(\\lambda.\\lambda.2\\)
both refer to the same free variable.

> freeVars :: Term -> [Int]
> freeVars t = Set.toList $ snd $ runWriter $ runReaderT (transform op t) 0
>     where op i = const (Ref i) <$> (ask >>= tell . Set.singleton . (i-))

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

In case we need multiple names, we can define `popNames` as follows:

> popNames :: MonadState Names m => Int -> m [String]
> popNames i = sequence $ replicate i popName

{{< todo >}}Elaborate here.{{< /todo >}}

> extendNames :: MonadReader [String] m => [String] -> m a -> m a
> extendNames ns m = foldr (local . (:)) m ns

And now, the pretty printer itself.

> instance Show Term where
>     show t = fst $ runState (runReaderT (showM t) []) names
>         where
>             showM (Ref i) = nth i <$> ask >>= maybe (return "??") return
>             showM (Abs t1 t2) = do
>                 newName <- popName
>                 st1 <- showM t1
>                 st2 <- extendNames [newName] $ showM t2
>                 return $ "λ(" ++ newName ++ ":" ++ st1 ++ ")." ++ st2
>             showM (App t1 t2) =
>                 liftA2 (\s1 s2 -> s1 ++ " (" ++ s2 ++ ")") (showM t1) (showM t2)
>             showM (Prod t1 t2) = do
>                 newName <- popName
>                 st1 <- showM t1
>                 st2 <- extendNames [newName] $ showM t2
>                 if occurs 0 t2
>                  then return $ "∀(" ++ newName ++ ":" ++ st1 ++ ")." ++ st2
>                  else return $ "(" ++ st1 ++ ") → " ++ st2
>             showM (Universe u) = return $ show u
>             showM (Constr i ci) = return $ maybe "??" cName $ nth ci (iConstructors i)
>             showM (Ind i) = return $ iName i
>             showM (Case t i tt ts) = do
>                 st <- showM t
>                 termName <- popName
>                 indexNames <- popNames (length $ iArity i)
>                 stt <- extendNames (termName:indexNames) (showM tt)
>                 sts <- zipWithM constr (iConstructors i) ts
>                 return $ "match " ++ st ++ " as " ++ termName ++ " in " ++ (intercalate " " $ iName i : indexNames) ++ " return " ++ stt ++ " with { " ++ intercalate "; " sts ++ " }"
>             constr c t = do
>                 paramNames <- popNames (length $ cParams c)
>                 st <- extendNames paramNames (showM t)
>                 return $ intercalate " " (cName c : paramNames) ++ " -> " ++ st

In the above, we used a function `nth`. This is just a safe version of the `(!!)` operator
that is built into Haskell. It'll come in handy in other modules, too.

> nth :: Int -> [a] -> Maybe a
> nth _ [] = Nothing
> nth 0 (x:xs) = Just x
> nth n (x:xs) = nth (n-1) xs
