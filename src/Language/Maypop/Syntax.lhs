Here, I'll define what a Maypop "term" is.

> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE DeriveFunctor #-}
> {-# LANGUAGE DeriveFoldable #-}
> {-# LANGUAGE DeriveTraversable #-}
> module Language.Maypop.Syntax where
> import Language.Maypop.InfiniteList
> import Control.Applicative
> import Control.Monad.Reader
> import Control.Monad.State
> import Control.Monad.Writer
> import Data.List
> import Data.Void
> import Data.Bifunctor
> import qualified Data.Set as Set

When writing a program in Maypop, a user will likely put down two types
of definitions: data types (pair, list, optional) and code (functions).
Both of these rely in some manner on terms (expressions) in the Maypop
language; we'll get to those shortly.

The first kind of definition that we will look at is that of inductive
data types. After all, it's the Calculus of _Inductive_ Constructions!
Our language will have inductive data types, more specifically inductive GADTs.
Each inductive data type accepts some parameters, an "arity" declaration,
and constructors. In general, the paper I'm using as reference defines the
following form (in Coq-like syntax):

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
a [type family indexed by terms](http://docs.idris-lang.org/en/latest/tutorial/typesfuns.html#vectors) in our language. Unlike the parameters,
the indexing terms _depend on the constructors_ of the data! For example,
in a `Vec` data type (like the one in Idris, see the above link),
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
(`iParams`), its arity (`iArity`, which we represent as just the
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

To be able to print (via `Show`) our various data structures,
it helps to either implement or derive `Show` for many of our
data structures. In the case of an inductive data type, we
simply show its name:

> instance Show Inductive where
>     show = iName

So those are data type definitions. The next type of definition is a function
definition. It would something like the following:

```
factorial : Nat -> Nat
factorial n =
    case n of
        O -> O
        (S n') -> n * factorial n'
```

Notice that this is not a term in itself; the above five lines don't
quite evaluate to anything. They do, however, tell the interpreter 
about a function `factorial`, and its body. They also provide
a tiny amount of extra information: the expected return type of the function.
In an explicitly typed lambda calculus, this information is not provided
by a lambda abstraction: the return type is computed from the body. It's nice,
if even from a documentation perspective, to immediately see the return type
of a function. We will thus follow this syntax, and check the expected
return type against the computed type of the function definition's body.

Before we get to that, though, let's define a data structure for a function
definition. This isn't particularly difficult; we need only the name,
arity (number of parameters), return type, and body of the function. Much
like we did with inductive types, we represent the arity by a list of types,
to ensure that every one of the function's arguments _actually_ has a type.
Representing arity in this way will also help us turn function definitions
into equivalent lambda abstractions.

> data Function = Function
>     { fName :: String
>     , fArity :: [Term]
>     , fType :: Term
>     , fBody :: Term
>     , fDec :: Maybe Int
>     }

It's always good to have in hand the _whole_ type of the function (`Args -> Return`).
This is a straightforward right-associative fold:

> fFullType :: Function -> Term
> fFullType f = foldr Prod (fType f) (fArity f)

One moment, though. What about the parameter names, like `n` from
the `factorial` example above? It so happens that we will be using DeBrujin
indices instead of strings for variable references. Thus, it 
{{< sidenote "right" "names-note" "doesn't do us much good" >}}
It would be good for debugging, of course. In our implementation, though,
we sidestep this particular issue for now.
{{< /sidenote >}} to keep track of what variable is named what.

Just like we did with inductive definitions, let's give `Function`
an `Eq` instance based on its name:

> instance Eq Function where
>     f1 == f2 = fName f1 == fName f2

When we are trying to print out a function, we typically only want its
name. Let's define a `Show` instance accordingly.

> instance Show Function where
>     show = fName

The Calculus of Inductive Constructions gives special treatment to recursive (fixpoint)
functions. This is because the evaluation rule of [\\(\\delta\\)-reduction](https://coq.github.io/doc/v8.9/refman/language/cic.html#delta-reduction) can cause serious trouble
with functions that contain their own name. In brief, \\(\\delta\\)-reduction substitutes
references to functions and constants with their definitions. If a function's definition
contains a reference to itself, this reference can be replaced by the function's body
using \\(\\delta\\)-reduction. This new instance of the function's body would again contain
the function's name, which can once again be \\(\\delta\\)-reduced. This can go infinitely,
creating bigger and bigger terms. We certainly don't want that.
To work around this, fixpoint functions are coupled with information about their "decreasing"
parameter. Recursive calls to a function within its body must always contain a "smaller"
argument than was given to them. For example, if `f l` is a function on lists, with `l`
being its decreasing parameter, it cannot recursively call itself as `f (Cons x l)`,
because `Cons x l` is bigger than `l`. We encode this as `fDec`, which contains the
index of the function's decresing argument, if any.

With the details of definitions out of the way, it's time to describe the terms in our language.
There's a little trick to the way that we will define them: we'll parameterize
our term datatype, making it, in general, a type constructor. We'll call this
type constructor `ParamTerm`. The paramter in the expression is the type of the unification
variables it may contain; `ParamTerm String` will contain all the constructs
in our language, as well as unification variables of type `String`. We don't
always want to allow unification variables in our expression (for instance,
they are meaningless in definitions of constructors and inductive data types). To represent
such variable-less expressions,
we will use `Void` as the type of unification variables. Since it is imposible
to construct an instance of type `Void`, it will be imposible to create a `ParamTerm Void`
that contains unification variables.

We'll be using [DeBrujin indices](https://en.wikipedia.org/wiki/De_Bruijn_index), so variables will not
be represented as strings (and thus, no need to perform any complicated alpha renaming). We have the following
terms in the language:

* **A reference to a variable**. The integer argument to the constructor is a DeBrujin index.
* **A reference to a global definition**. This will behave differently from
references to function arguments and the like.
* **A lambda abstraction**. There's no need to provide a variable name for this abstraction (once again, because of DeBrujin indexing), but
{{< sidenote "right" "explicit-lambda-note" "we do need to provide a type for the parameter." >}}
The core Calculus of Inductive Constructions is explicitly typed. This is why we need to specify
the type of the lambda function's parameter.
{{< /sidenote >}} Thus, the first term is the type, and the second term is the body of the lambda.
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

> data ParamTerm a
>     = Ref Int
>     | Fun Function
>     | Param a
>     | Abs (ParamTerm a) (ParamTerm a)
>     | App (ParamTerm a) (ParamTerm a)
>     | Let (ParamTerm a) (ParamTerm a)
>     | Prod (ParamTerm a) (ParamTerm a)
>     | Sort Sort
>     | Constr Inductive Int
>     | Ind Inductive
>     | Case (ParamTerm a) Inductive (ParamTerm a) [(ParamTerm a)]
>     deriving (Eq, Show, Functor, Foldable, Traversable)
>
> type Term = ParamTerm Void

For convenience, we combine the references to the various
sorts (\\(\\text{Prop}\\) and \\(\\text{Type}_n\\)) into a data type,
`Sort`:

> data Sort = Prop | Type Int deriving (Eq, Show)

If we have a term without parameters (`Term`), we can always
interpret it as a term that may contain parameters. We can always
trivially translate from `Void` into any other type `a` using
the `abusrd` function, so this re-interpretation is define as follows:

> parameterize :: Term -> ParamTerm a
> parameterize = fmap absurd

It's not uncommon to have to parameterize an entire list of
terms, for which we provide another helper function as follows:

> parameterizeAll :: [Term] -> [ParamTerm a]
> parameterizeAll = map parameterize

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
of surrounding [binders](https://en.wikipedia.org/wiki/Lambda_calculus#Free_and_bound_variables). When case expressions come into play,
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

> transform
>     :: MonadReader Int m
>     => (Int -> m (ParamTerm a)) -> ParamTerm a -> m (ParamTerm a)
> transform f = local (const 0) . trans
>     where
>         trans (Ref m) = ask >>= \x -> if m >= x then f m else return (Ref m)
>         trans (Abs t1 t2) = liftA2 Abs (trans t1) (deepen 1 $ trans t2)
>         trans (App t1 t2) = liftA2 App (trans t1) (trans t2)
>         trans (Let t1 t2) = liftA2 Let (trans t1) (deepen 1 $ trans t2)
>         trans (Prod t1 t2) = liftA2 Prod (trans t1) (deepen 1 $ trans t2)
>         trans (Case t i tt ts) = do
>             t' <- trans t
>             tt' <- deepen (1 + length (iArity i)) $ trans tt
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

Finally, we can define substitution. Given a DeBrujin index `i` with
`x` surrounding binders, if `i-x` is equal to the target substitution
index `n`, we perform substitution; otherwise, we perform the "safe decrement"
operation described earlier.

> substitute :: Int -> ParamTerm a -> ParamTerm a -> ParamTerm a
> substitute n t r = runReader (transform op r) 0
>     where op i = (\x -> if i == n + x then offsetFree x t else Ref $ safeDec n x 1 i) <$> ask

What if we want to substitute multiple terms terms at the same time?
Simply composing calls to `substitute` is not good enough, because a free variable introduced
by one term may be another target for substitution. To accomodate multiple substitutions,
we can write another helper function, `substituteMany`:

> substituteMany :: Int -> [ParamTerm a] -> ParamTerm a -> ParamTerm a
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

> offsetFree :: Int -> ParamTerm a -> ParamTerm a
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

> freeVars :: ParamTerm a -> [Int]
> freeVars t = Set.toList $ snd $ runWriter $ runReaderT (transform op t) 0
>     where op i = const (Ref i) <$> (ask >>= tell . Set.singleton . (i-))

Since `freeVars` finds _all_ free variables in a term, checking if a single variable
occurs free becomes as simple as looking inside that list.

> occurs :: Int -> ParamTerm a -> Bool
> occurs i = elem i . freeVars

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
and so on. We don't actually do this here; it so happens that such an infinite
list can also be used in other parts of Maypop. Things that have associated
infinite lists are instances of the `Infinite` typeclass (also defined
in the `InfiniteList` module); we use `String`'s instance to create
our list of names:

> names :: Names
> names = infList

In our implementation, an `Inf` monad (which gives us the function `pop`
that retrieves a value from an infinite list)
will be used to generate more and more fresh variable, and a `Reader`
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

> pretty :: (Show a, Eq a) => ParamTerm a -> String
> pretty t = runInf (runReaderT (prettyM 0 t) [])
>     where
>         collectProd (Prod l r) | occurs 0 r = first (l:) $ collectProd r
>         collectProd e = ([], e)
>         prettyMGroup xs rm = do
>             names <- popN (length xs)
>             st <- maybe (return "??") (prettyM 0) (nth 0 xs)
>             sr <- extendNames names rm
>             return $ "∀(" ++ intercalate " " names ++ " : " ++ st ++ ")." ++ sr
>         paren b s = if b then "(" ++ s ++ ")" else s
>         prettyM _ (Ref i) = nth i <$> ask >>= maybe (return $ "??" ++ show i) return
>         prettyM _ (Fun f) = return $ fName f
>         prettyM _ (Param p) = return $ show p
>         prettyM n (Abs t1 t2) = paren (n >= 10) <$> do
>             newName <- pop
>             st1 <- prettyM 0 t1
>             st2 <- extendNames [newName] $ prettyM 0 t2
>             return $ "λ(" ++ newName ++ ":" ++ st1 ++ ")." ++ st2
>         prettyM n (App t1 t2) = paren (n >= 11) <$> do
>             st1 <- prettyM 10 t1
>             st2 <- prettyM 11 t2
>             return $ st1 ++ " " ++ st2
>         prettyM n t@(Prod t1 t2) = do
>             if occurs 0 t2
>              then paren (n >= 10) <$> do
>                  let (ps, rt) = collectProd t
>                  let pgs = groupBy (\t1 t2 -> offsetFree 1 t1 == t2) ps
>                  foldr prettyMGroup (prettyM 0 rt) pgs
>              else paren (n >= 10) <$> do
>                  st1 <- prettyM 10 t1
>                  st2 <- extendNames ["_"] $ prettyM 9 t2
>                  return $ st1 ++ " → " ++ st2
>         prettyM n (Let t1 t2) = paren (n >= 10) <$> do
>             newName <- pop
>             st1 <- prettyM 0 t1
>             st2 <- extendNames [newName] $ prettyM 0 t2
>             return $ "let " ++ newName ++ " = " ++ st1 ++ " in " ++ st2
>         prettyM _ (Sort u) = return $ show u
>         prettyM _ (Constr i ci) = return $ maybe "??" cName $ nth ci (iConstructors i)
>         prettyM _ (Ind i) = return $ iName i
>         prettyM n (Case t i tt ts) = paren (n >= 10) <$> do
>             st <- prettyM 0 t
>             termName <- pop
>             indexNames <- popN (length $ iArity i)
>             stt <- extendNames (termName:indexNames) (prettyM 0 tt)
>             sts <- zipWithM constr (iConstructors i) ts
>             return $ "match " ++ st ++ " as " ++ termName ++ " in " ++ (intercalate " " $ iName i : indexNames) ++ " return " ++ stt ++ " with { " ++ intercalate "; " sts ++ " }"
>         constr c t = do
>             paramNames <- popN (length $ cParams c)
>             st <- extendNames paramNames (prettyM 0 t)
>             return $ intercalate " " (cName c : paramNames) ++ " -> " ++ st

{{< sidenote "right" "voila-note" "Et Voila." >}}In homage to the last page of <a href="https://babel.ls.fi.upm.es/~pablo/Papers/Notes/f-fw.pdf">Nogueira, 2006</a>{{</ sidenote >}}

In the above, we used a function `nth`. This is just a safe version of the `(!!)` operator
that is built into Haskell. It'll come in handy in other modules, too.

> nth :: Int -> [a] -> Maybe a
> nth _ [] = Nothing
> nth 0 (x:_) = Just x
> nth n (_:xs) = nth (n-1) xs
