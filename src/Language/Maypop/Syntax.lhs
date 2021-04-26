Here, I'll define what a Maypop "term" is.

{{< todo >}}Inductive stuff has names? How does equality work?{{< /todo >}}
{{< todo >}}Introduce binders.{{< /todo >}}

> {-# LANGUAGE FlexibleContexts #-}
> module Language.Maypop.Syntax where
> import Language.Maypop.InfiniteList
> import Control.Applicative
> import Control.Monad.Reader
> import Control.Monad.Except
> import Control.Monad.State
> import Control.Monad.Writer
> import Data.Bool
> import Data.List
> import qualified Data.Set as Set
>

### Inductive Types
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
a type family indexed by terms in our language. Unlike the parameters,
the indexing terms _depend on the constructors_ of the data! For example,
in a `Vec` data type (like [the one in Idris](http://docs.idris-lang.org/en/latest/tutorial/typesfuns.html#vectors)),
the `Nil` constructor will have type `Vec Int 0`, but the `Cons` constructor
will produce a value of type `Vec Int (n+1)`. We thus cannot count the length
as a _parameter_ (as all contructors would then have to have the same length),
but we _can_ specify the type of this argument. This is the point of the arity:
it tells us the types of the indices which differ for each constructors,
denoted `B1` through `Bm` in the above code snippet.

Once all the parameters and indices are applied to a type constructor,
it returns a type. What is the sort of this type? Is the new type
a `Prop`, that is, a kind of proposition? Or is the new type a
`Type 0`, that is,
{{< sidenote "right" "impredicative-note" "a regular type?" >}}
What's the difference between <code>Prop</code> and <code>Type 0</code>?
Fundamentally, <code>Prop</code> is impredicative; things of sort
<code>Prop</code> can be built from things quantified over <code>Prop</code>.
This is a dangerous property, because it can quickly lead to inconsistent logical
sytems (which we don't want, since we want to be able to prove things
using Maypop). To combat this, all other sorts, like <code>Type 0</code>,
are <em>not</em> impredicative.
{{< /sidenote >}}
We explicitly specify the sort returned from the type constructor;
in the general definition, we refer to it as `s`.

Finally, we have constructors. Constructors can take more arguments
than have already been given via the parameters: the `Cons` constructor
of the above `List`, for instance, would accept two additional parameters, one
of type `t` and one of type `List t`. The `Nil` constructor, on the other hand,
would accept no additional parameters. Finally, each constructor must
return the type family defined by the data type, applied to the aforementioned
indexing terms: as I mentioned above, the `Vec` version of `Nil` returns `Vec Int 0`,
and `Cons` returns `Vec Int (n+1)`.

We encode all this in the following two data type definitions. In our view,
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
>     , iSort :: Sort
>     , iConstructors :: [Constructor]
>     , iName :: String
>     }

Equality on data types is required, but hard to provide. For now, We'll
just compare their names.

> instance Eq Inductive where
>     i1 == i2 = iName i1 == iName i2

{{< todo >}}Debug! Delete below instance. {{< /todo >}}

> instance Show Inductive where
>     show = iName

### Terms
With the details of inductive types out of the way, it's time to describe the terms in our language.
We'll be using [DeBrujin indices](https://en.wikipedia.org/wiki/De_Bruijn_index), so there will be
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
* **A dependent product**, which is a generalization of a function type. Once again, there's no need to define a variable, but there _is_ a need to provide the input and output type. Unlike a regular function, a dependent
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
>     | Sort Sort
>     | Constr Inductive Int
>     | Ind Inductive
>     | Case Term Inductive Term [Term]
>     deriving Eq

For convenience, we combine the references to the various
sorts (\\(\\text{Prop}\\) and \\(\\text{Type}_n\\)) into a data type,
`Sort`:

> data Sort = Prop | Type Int deriving (Eq, Show)

### Substitution etc., __etc.__
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

Substitution is a special case of this kind of transformation. When encountering the
target free variable, it replaces it with the given term `t`. There's a little
nuance to this: we want to decrement free variables in the _target_ term
(because we're effectively removing a lambda abstraction), but we don't want to
decrement them in the term being substituted, since it hasn't changed. However,
after substittion occurs, there's no way to tell which part of the resulting
expression was there originally and which was placed there. Thus, we have
to perform substitution and decrements in one go.

There's another concern, too. If we substitute for the free variable other
than the "shortest" one (that is, the one with the smallest DeBrujin index),
we run the risk of turning free variables into bound variables when decrementing.
Consider something like \\((\\lambda.1 \\ 2)[1 := \\lambda.0]\\), where we
replace the second "shortest" variable with the identity function. If we decrement
the free variables, we end up with \\(\\lambda.0 \\ \\lambda.0\\). There are no
free variables in this term! We only need to decrement free variables
larger than the one we're substituting. We can encapsulate this functionality
in a helper function `safeDec`:

> safeDec :: Int -> Int -> Int -> Int -> Int
> safeDec n x b i | i > n + x = i - b
> safeDec _ _ _ i = i

Finally, we can define substitution:

> substitute :: Int -> Term -> Term -> Term
> substitute n t r = runReader (transform op r) 0
>     where op i = (\x -> if i == n + x then offsetFree x t else Ref $ safeDec n x 1 i) <$> ask

What if we want to substitute multiple terms terms at the same time?
Simply composing calls to `substitute` is not good enough, because a free variable introduced
by one term may be another target for substitution. To accomodate multiple substitutions,
we can write another helper function, `substituteMany`:

> substituteMany :: Int -> [Term] -> Term -> Term
> substituteMany n ts r = runReader (transform op r) 0
>     where
>         sub = zip [n..] (reverse ts)
>         off = length ts
>         op i = (\x -> maybe (Ref $ safeDec n x off i) (offsetFree x) $ lookup (i-x) sub) <$> ask

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

### A Pretty Printer
How about a pretty printer? Our language is simple enough. To make our expressions
more readable to humans, we will use an infinite list of variable names, and
assign to each abstraction a fresh name. It's conventional to distinguish different
types of variables (plain variables, type variables) by using a different alphabet,
but this requires typechecking, and that's a lot more work than I think a pretty printer
should do. Thus, we'll just use a simple, infinite, list of names, using our
`InfiniteList` module and its `InfList` type:

> type Names = InfList String

Finally, we define an infinite list of names, which first consists
of all single-letter names, and then all two letter names (alphabetically ordered),
and so on.

> names :: Names
> names = fromList (map return alphabet) $ expand (\s -> ((s++) . return) <$> alphabet) names
>     where alphabet = ['a'..'z']

Now we have all the machinery in place for wrangling our infinite
list of varaible names. We'll be using a State monad to keep track
of which names we have and haven't used. We can thus write a convenient
operation to generate a fresh name in such a context. This operation
generates a new name (by peeking at the infinite list of names via `headInf`)
and then removes it from the list (by setting the name list to its tail via `tailInf`).

> popName :: MonadState Names m => m String
> popName = gets headInf <* modify tailInf

In case we need multiple names, we can define `popNames` as follows:

> popNames :: MonadState Names m => Int -> m [String]
> popNames i = sequence $ replicate i popName

We now have ways to generate fresh names; what remains is a way to
make these names available to our pretty printer. While the `State`
mond will be used to generate more and more fresh variable, a `Reader`
monad will be used to represent the names corresponding to each DeBrujin
index. This is simple enough to represent as a stack of names:
the top name on the stack corresponds to DeBrujin index 0, the
second name corresponds to DeBrujin index 1, and so on. When entering
a lambda abstraction, we push a new varialbe name onto the stack,
thus introducing a name for the new parameter, and at the same
time offsetting the names of the previously existing parameters.

It's easiest to define an operation that extends the stack with many
names at once. Here and elsewhere, __I'll adopt the convention
that the rightmost name / element in a list should correspond
to the smallest DeBrujin index__. This corresponds to the intuition
that in the term \\(\\lambda a. \\lambda b. \\lambda c. a \\ b \\ c\\),
the equivalent DeBrujin index will be 0 for \\(c\\), 1 for \\(b\\),
and 2 for \\(a\\).

> extendNames :: MonadReader [String] m => [String] -> m a -> m a
> extendNames ns = local (reverse ns++)

And now, the pretty printer itself.

> instance Show Term where
>     show t = fst $ runState (runReaderT (showM t) []) names
>         where
>             showM (Ref i) = nth i <$> ask >>= maybe (return $ "??" ++ show i) return
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
>             showM (Sort u) = return $ show u
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
