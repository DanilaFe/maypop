In this module, we convert parsed expressions into valid Maypop terms, by
resolving references to various variables to either their corresponding
function objects or their DeBrujin indices.

> {-# LANGUAGE RecursiveDo #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE MonoLocalBinds #-}
> module Language.Maypop.Resolver where
> import Prelude hiding (pi)
> import Language.Maypop.Syntax hiding (ParamTerm(..), Term)
> import qualified Language.Maypop.Syntax as S
> import Language.Maypop.Modules
> import Language.Maypop.Parser
> import Language.Maypop.Unification
> import Language.Maypop.Context
> import Language.Maypop.InfiniteList
> import Language.Maypop.Checking hiding (NotInductive)
> import Control.Applicative hiding ((<|>), many)
> import Control.Monad.Reader
> import Control.Monad.State
> import Control.Monad.Except
> import Text.Parsec
> import Text.Parsec.Token
> import Text.Parsec.Expr
> import Text.Parsec.Indent
> import qualified Data.Map as Map
> import qualified Data.Set as Set
> import Data.Char
> import Data.Monoid
> import Data.Bifunctor
> import Data.List
> import Data.Maybe
> import Data.Functor.Identity
> import Data.Either

Turning parsed expressions into their `Term` coutnerparts
can go wrong in many different ways. We first define a data
type to represent all the possible errors. Note in particular
the `InferError` constructor, which wraps a `TypeError`. Filling
in implicit arguments is based on types; we thus have to perform
type inference, which can itself yield a variety of errors.

> data ResolveError
>     = UnknownReference
>     | AmbiguousReference
>     | NotInductive
>     | InvalidArity
>     | IncompleteMatch
>     | ImportError ImportError
>     | InferError TypeError
>     | InvalidFixpoint
>     | InvalidResolve
>     deriving Show

An important concept in the Calculus of Inductive Constructions
is the notion of fixpoints. These are functions bundled with their
"decreasing" argument, which are used for recursion. There are restrictions
on how these functions are evaluated, which helps prevent unwanted infinite
substitutions. To construct these fixpoints, we will need to track the "sizes" of the various
arguments to function calls so that we can determine the decreasing
argument, if any. For instance, a definition like `f x = f x` will not
be valid, since none of the parameters to the recursive call to `f` are
"smaller" than the original parameters (in fact, they're the same size!). On the
other hand, something like `f (x:xs) = f xs` would be okay, since `xs` is a part
of the original list, and thus smaller. By forcing a function to have
a decreasing argument, we effectively force it to terminate: the argument keeps
getting smaller, and will eventually exhaust itself.

To track the sizes of various references, we will bundle a new data type, `VarSize`,
with variables we encounter. In addition to `Original` (the size of a parameter itself)
and `SmallerThan x` (the size of a variable that's smaller than input parameter `x`),
we also use the `Self` size to indicate recursion (in our above examples, `f` would
have size `Original`). This third size will help absolve us of the need to insert
`Fun` or `Ind` constructors referring to the current definition (for instance,
in recursive functions). That's not to say that inserting such recursive references
is impossible: recursive functions are invariably represented by cyclic data structures
in our encoding of the language. However, creating such cyclic data structures
right off the bat is more complicated and not particularly worth it.

> data VarSize = Self | Original | SmallerThan String | Unknown deriving Show

We also define a handy helper function that, if the current variable
is "smaller" than some other variable, returns that other variable.

> varParent :: VarSize -> Maybe String
> varParent (SmallerThan s) = Just s
> varParent _ = Nothing

We will not go straight from `ParseTerm` to `Term` while resolving. There is
another intermediate step: inserting "inferred" function arguments. For instance,
the parsed expression `id O` will first be translated to `id _ O` (inserting
a placeholder for the type we need to infer), and then be elaborated into
`id Nat O` after a round of type checking. To represent expressions
such as `id _ O`, we define a data type `ResolveParam`, which is used
to parameterize `ParamTerm`. This data type also has an extra
constructor, `SelfRef`, which will be used as a stand-in for a recursive
function call or self-reference.

> data ResolveParam = SelfRef | Placeholder deriving (Eq, Show)
> type ResolveTerm = S.ParamTerm ResolveParam

In several places, it will be helpful to be aware of the current
definition that we are trying to resolve. For these situations,
we define `CurrentInd` and `CurrentFun`, which contain
useful information such as the types of the definition's parameters (and
posibly indices), as well as the definition's textual form (as `ParseInd`
or `ParseFun`).

> data CurrentInd = CurrentInd
>     { ciParams :: [S.Term]
>     , ciIndices :: [S.Term]
>     , ciParsed :: ParseInd
>     }
>
> data CurrentFun = CurrentFun
>     { cfParams :: [S.Term]
>     , cfParsed :: ParseFun
>     }

Another data type, `CurrentDef`, contains information that's common
to every definition. Note that instead of just having a `cdTerm`
field, which contains the term of the current definition, we have
`cdFutureTerm`. And indeed, if we think about it, that's exactly what it is:
we're in the middle of resolving a definition, so when we have a reference to it,
it's like we're holding something from the future in our hands. But how 
_can_ we have a reference to a term from the future? It's a bit out of scope
for this page, but check out [Csongor Kiss'](https://blog.csongor.co.uk/time-travel-in-haskell-for-dummies/) article
on the technique that allows this (time traveling!), and maybe also [this article of mine](https://danilafe.com/blog/haskell_lazy_evaluation/).

The main thing to know about handling such future values is that __we cannot make decisions based on them__.
This is because intuitively, we cannot base our decision on its future outcone.
If this is too philosophical, you can think about what happens under the hood: our future
value is not actually a value, but a [thunk](https://wiki.haskell.org/Thunk). When time traveling, this thunk
contains a reference to itself. Then, To make a decision based on our future term,
we need to evaluate the thunk to a value. But the thunk contains itself, and
evaluating it requires making that decision, which once again requires evaluating
the thunk. We end up in an infinite loop. Sometimes, Haskell kindly lets us know
we've done so, and crashes with error message `<<loop>>`. Other times,
our program will simply hang. Neither outcome is desirable.

> data CurrentDef = CurrentDef
>     { cdFutureTerm :: S.Term
>     , cdType :: S.Term
>     , cdExtra :: Either CurrentInd CurrentFun
>     }

Now we have our various encodings of the current definition. Next, we move
on to defining the resolver's environment, which will be kept inside
a `Reader` monad. The reason we need an environment is that the translation
of the parsed term \\(x\\) depends on what surrounds it: 
if the whole expression is \\(\\lambda x. x\\), we translate \\(x\\)
to \\(0\\), yielding \\(\\lambda. 0\\). However, when the whole expression
is \\(\\lambda x. \\lambda y. x\\), we translate \\(x\\) to \\(1\\),
and the whole expression to \\(\\lambda.\\lambda.1\\). We thus keep
a stack of names associated with binders; when a name is on the top
of a stack, it was introduced last, and thus should be translated
to index \\(0\\); the second name from the top was introduced second-to-last,
and should thus be translated to index \\(1\\). We name his stack `reVars`.

Another "dynamic" piece of data is `reApps`. Whereas `reVars` effectively
tracks the __binders__ around the current term, `reApps` tracks the
__applications__. Thus, in the expression \\(f\\ x\\ y\\), when we translate
\\(f\\), our `reApps` will include \\(x\\) and \\(y\\). We need this
to track decreasing arguments to functions: when we encounter a recursive
call, we check what arguments it's applied to, and record which, if any, are
smaller versions of the original arguments. Then, at the end, if we find
that one argument always receives a "smaller" value, we know we're safe:
our function will eventually terminate. If, on the other hand, no argument
is consistently smaller, we will give up and report `InvalidFixpoint`.

The remaining two fields of our environment are `reHeader` (currently
only used to retrieve the current module name) and `reCurrentDef`,
the current definition data sturcutre we've defined above.

> data ResolveEnv = ResolveEnv
>     { reVars :: [(String, VarSize)]
>     , reHeader :: ModuleHeader
>     , reCurrentDef :: Maybe CurrentDef
>     , reApps :: [ParseTerm]
>     }

Time for some functions that run a monadic computation `m a` in a modified `ResolveEnv`.
The first of these many functions is `withSizedVar`, which pushes a new variable
onto the stack, making it visible within the input computation, assigning to it
the index \\(0\\), and shifting the indices of the other variables' indices by one.
In addition to the variable name, this function also adds the variable's size information:
whether it's smaller, a recursive reference, or unknown.

> withSizedVar :: MonadReader ResolveEnv m => VarSize -> String -> m a -> m a
> withSizedVar vs s = local (\re -> re { reVars = (s,vs) : reVars re })

As a shortcut for the case when we are introducing a variable with no known
size information, we define `withVar` as follows:

> withVar :: MonadReader ResolveEnv m => String -> m a -> m a
> withVar = withSizedVar Unknown

Sometimes we need to introduce more than a single variable in the environment
at the same time (when processing case expression branches, for instance). We thus
define a helper function `withSizedVars`, that simply repeats `withSizedVar`
for each variable in its input.

> withSizedVars :: MonadReader ResolveEnv m => VarSize -> [String] -> m a -> m a
> withSizedVars vs xs m = foldr (withSizedVar vs) m xs

Of course, we also define the "easy" version of the above, where all the variables
are set to `Unknown`.

> withVars :: MonadReader ResolveEnv m => [String] -> m a -> m a
> withVars xs m = foldr withVar m xs

Next up, we define a way to set the `reCurrentDef` field to a definition. Such functions
take a lot of arguments: the `cdFutureTerm` that represents a handle on
the resulting definition, the `cdType` that represents (unsurprisingly) the definition's type,
and some definition-specific parameters. For instance, the `withFun` function also accepts
a list of the function's parameters and the raw version of the function that we received from
the parser.

> withFun :: MonadReader ResolveEnv m => S.Term -> S.Term -> [S.Term] -> ParseFun -> m a -> m a
> withFun t tt ps f = local $ \re -> re { reCurrentDef = Just (CurrentDef t tt $ Right $ CurrentFun ps f) }

If we're entering the body of a function, there are a few other things we might want to do other
than just set the `reCurrentDef` field. Since we're likely about to resolve the function's body,
we also want to introduce the function's parameters (all tagged `Original`, since they
are the inputs to our function), as well as the function itself (tagged `Self` to indicate
recursion). We combine all of these operations into `withFunction`.

> withFunction :: MonadReader ResolveEnv m => S.Term -> S.Term -> [S.Term] -> ParseFun -> m a -> m a
> withFunction t tt ps f = withFun t tt ps f . withSizedVar Self (pfName f) . withSizedVars Original (pfParamNames f)

Similarly to `withFun`, the `withInd` function accepts, in addition to the term and its type, the list
of the inductive definition's parameters, index types, and the raw version of the inductive
definition received from the parser.

> withInd :: MonadReader ResolveEnv m => S.Term -> S.Term -> [S.Term] -> [S.Term] -> ParseInd -> m a -> m a
> withInd t tt ps is i = local $ \re -> re { reCurrentDef = Just (CurrentDef t tt $ Left $ CurrentInd ps is i) }

Just as with `withFunction`, we define a `withInductive` function that not only sets the current
definition to an inductive data type, but also introduces its parameters -- along with a reference
to the data type itself -- into the environment. This time we don't bother tagging the parameters
as `Original`, since we need not detect recursion for data types.

> withInductive :: MonadReader ResolveEnv m => S.Term -> S.Term -> [S.Term] -> [S.Term] -> ParseInd -> m a -> m a
> withInductive t tt ps is pi = withInd t tt ps is pi . withSizedVar Self (piName pi) . withVars (piParamNames pi)

We're almost done with environment modifiers! The last couple of modifiers deal with the
`reApps` field of our environment. The first is called `withApp`, which lets us know
that we have descended into the right hand side of an application, and thus the current
term we're considering is applied to one more argument.

> withApp :: MonadReader ResolveEnv m => ParseTerm -> m a -> m a
> withApp pt = local $ \re -> re { reApps = pt : reApps re }

If we descend into something like a lambda abstraction, whatever terms were
applied to the current term are no longer meaningful (it's more complicated
to track the sizes of variable across aliasing). To be safe rather than sorry,
we discard all applications so far when processing such terms. This is strictly
a conservative strategy, since it will never cause false positive decreasing
arguments, but may
{{< sidenote "right" "fixpoint-note" "fail to detect valid instances of recursion." >}}
Indeed, even "real" languages like Coq have this problem. Some "elegant" ways of
defining functions are ruled out by the termination checker. Some  languages (Coq included)
allow you to manually prove termination, by specifying a "measure" on one or more of your arguments,
and proving that it decreases with every function call. We will not do so, however, since such
features are rather complicated.
{{< /sidenote >}}

> clearApps :: MonadReader ResolveEnv m => m a -> m a
> clearApps = local $ \re -> re { reApps = [] }

With modification out of the way, we're left with retrieval. Our first
function of this kind is `currentModule`, which retrieves the current module's
name, in the form of a `Symbol`. This helps us when we want to add a definition
we just resolved to the environment for other definitions to use. Since we have the `reHeader`
field in the `ResolveEnv`, all we need to do is retrieve the header's name:

> currentModule :: MonadReader ResolveEnv m => m Symbol
> currentModule = asks (mhName . reHeader)

A bit more involved is looking up a variable in our stack of binders. This is because
we want to distinguish an important case from all others: a recursive self-reference.
To make this distinction, we first try to see if the variable we are looking up
has size `Self`; if it is, we return `Left ()`, which we take to mean "recursive reference".
If the variable we find does not have size `Self`, we instead fall back to finding
the variable's index in the stack using `elemIndex`, and wrapping it in `Right`.
To implement the "try one, then the other" behavior, we wrap the results of our
`findRef` and `findSelf` functions (both of which are initially `Maybe`s) in a `First`,
which is simply a `newtype` over `Maybe` that captures this behavior in its `Monoid` instance.

> lookupVar :: MonadReader ResolveEnv m => String -> m (Maybe (Either () Int))
> lookupVar s = asks (getFirst . (findSelf <> findRef) . reVars)
>     where
>         findRef = First . fmap Right . elemIndex s . map fst
>         findSelf = First . (>>= intoSelf) . lookup s
>         intoSelf Self = Just (Left ())
>         intoSelf _ = Nothing

Other than looking up a variable's DeBrujin index, we may also want to know its
size. This is handled by the below `varSize` function.

> varSize :: MonadReader ResolveEnv m => String -> m VarSize
> varSize s = asks (fromMaybe Unknown . lookup s . reVars)

Now, we get to a pretty interesting part of this module: our implementation
of simple type inference. We have already seen the definition of `ResolveTerm`,
a parameterization of `Term` that also includes special indicators of "holes",
like the `_` in `id _ 0`. While resolution initially produces these `ResolveTerm`
instances, this is not enough to perform type inference. What we're missing is
a way to "fill" particular holes: each occurence of `Placeholder` in `ResolveTerm`
is indistinguishable from every other such occurence. To remedy this, we assume
that we have access to a unification context, and, also assuming that each `Placeholder` is
different, replace each instance with a fresh unification variable. What remains is to handle
the case for `SelfRef`. In this situation, we assume that we have already picked some
concrete unification variable to stand for the self reference, and replace all instances
of `SelfRef` with that variable. Of course, it may happen that we don't allow a `SelfReference`
in a particular term. In this case, our unification variable is `Nothing`, and encountering
`SelfRef` results in failure via `mzero`.

> instantiate :: MonadInfer k m => Maybe k -> ResolveTerm -> m (S.ParamTerm k)
> instantiate mt = traverse inst
>     where
>         self = maybe mzero return mt
>         inst SelfRef = self
>         inst Placeholder = fresh

Once we're done performing type inference on our instantiated terms, we must ensure
that there are no unification variables in our expression that are not bound to something:
this would mean that we weren't able to infer parts of the expression, and it is thus invalid.
We define a function `strip` to turn any occurence of `SelfRef` or `Placeholder` (i.e.,
anything in a `Param` constructor) into an error.

{{< todo >}}
Reify with offset? Explain why.
{{< /todo >}}

> strip :: MonadInfer k m => Int -> S.ParamTerm k -> m S.Term
> strip i t = reifyTermOffset i t >>= traverse (const mzero)

Most unification variables end up substituted for actual expressions in
the process of reification, captured above by `reifyTermOffset`. However,
we can't use this mechanism for self-references, because doing so causes
time traveling errors of the kind mentioned above. Thus, we define a function
to simply susbtitute a particular term for a particular key.

{{< todo >}}
Verify again that we can't use reification.
{{< /todo >}}

> subst :: Eq k => k -> S.Term -> S.ParamTerm k -> S.ParamTerm k
> subst k t = subst'
>     where
>         subst' (S.Param k') | k == k' = parameterize t
>         subst' (S.Abs l r) = S.Abs (subst' l) (subst' r)
>         subst' (S.App l r) = S.App (subst' l) (subst' r)
>         subst' (S.Let l r) = S.Let (subst' l) (subst' r)
>         subst' (S.Prod l r) = S.Prod (subst' l) (subst' r)
>         subst' (S.Case t i tt ts) = S.Case (subst' t) i (subst' tt) (map subst' ts)
>         subst' t = t

Our above `instantiate` function requires a unificaton variable given to
it as argument if our expression can contain references to its own definition.
We need a function to create such a variable, which we'll call `mkSelf`. This
function explicitly specifies that our self-reference is valid in the empty context
(global definitions aside), unifies its type with a non-parameterized
`S.Term`, but leaves its value unknown.

> mkSelf :: MonadInfer k m => S.Term -> m k
> mkSelf t = do
>     k <- fresh
>     bind k (Context [] (Just $ parameterize t) Nothing)
>     return k

We wrap `mkSelf` by another function, `mkMSelf`, which handles the
case in which we don't, after all, need a self reference.

> mkMSelf :: MonadInfer k m => Maybe S.Term -> m (Maybe k) 
> mkMSelf = traverse mkSelf

Expression resolution is, unfortunately, not strictly environment-based; there's
a component of mutable state to it. For instance, each time we encounter a recursive
call, we want to augment our state, recording all the decreasing arguments (in fact,
we perform an intersection on the sets of decreasing arguments, thus making our state
contain only valid canidates for "decreasing argument"). We also keep track of the definitions
that were introduced while resolving the current module (so that we can eventually bundle them
into a new module record), and the current scope, which contains definitions imported from
other modules, as well as ones introduced in the current module.

> data ResolveState = ResolveState
>     { rsScope :: GlobalScope
>     , rsDefs :: Map.Map String Definition
>     , rsDecreasing :: Maybe (Set.Set String)
>     }

Resolution occurs within a `Monad`, one that contains our environment (`MonadReader ResolveEnv`) as
well as the current state (`MonadState ResolveState`), and supports failing (`MonadError ResolveError`).
In addition to these rather unsurprising constraints, we also have a newcomer: `MonadFix`. `MonadFix`
denotes the class of monads that can be used for time traveling, that is, monads that can hold references
to the future results of their computation. We combine these into a single alias, `MonadResolver`.

> class (MonadReader ResolveEnv m, MonadState ResolveState m, MonadError ResolveError m, MonadFix m)
>     => MonadResolver m where
>
> instance (MonadReader ResolveEnv m, MonadState ResolveState m, MonadError ResolveError m, MonadFix m)
>     => MonadResolver m where

Next, we'll write some code to perform type inference (including instantiation, type checking, and stripping of
terms) in the monadic context with `MonadResolver`. The first thing we can get started on is retriving
the current definition, be it an inductive data type or a function, which will eventually be used for
`mkMSelf`, as well as for getting a handle on the `futureTerm`. First up is `selfInductive`, which
requires that our current definition is set to something, and that this something is an inductive data type.

> selfInductive :: MonadResolver m => m (CurrentDef, CurrentInd)
> selfInductive = do
>     mcd <- asks reCurrentDef
>     case mcd of
>         Just cd@CurrentDef{cdExtra=Left ci} -> return (cd, ci)
>         _ -> throwError InvalidResolve

Symmetrically, we define `selfFunction`, which requires that our current definition is set to something,
and that _this_ something is a function definition.

> selfFunction :: MonadResolver m => m (CurrentDef, CurrentFun)
> selfFunction = do
>     mcd <- asks reCurrentDef
>     case mcd of
>         Just cd@CurrentDef{cdExtra=Right cf} -> return (cd, cf)
>         _ -> throwError InvalidResolve

Next, we arrive at the driving function of the elaboration code. Elaboration is the process
of convering an expression with placeholders (`ResolveTerm`) into an expression without placeholders
(`S.Term`) by filling in the holes created by the placeholders. Importantly, we may be elaborating an expression
within a non-empty environment (for instance, we may be elaborating a function's body, which requires access
to the function's arguments for typechecking to work). For this reason, we call our driving function `elaborateInEnv`.

Besides the environment and the term being resolved (both of which are actually accepted as `ResolveTerm`s, for
reasons that will become clear shortly), this function also accepts a `Maybe (S.Term, S.Term)`. This argument, like
many of the `Maybe`s we've encountered so far in this module, represents the current definition (with `Nothing`
meaning that the current definition is not available within the expression being elaborated). Unlike the
`Maybe S.Term` in `mkMSelf`, though, this argument also contains a reference to the future term, which
is eventually substituted into the resolved expression.

As we have observed above, an expression may be elaborated within a particular context. Rather than manually
keeping track of this context everywhere in our `MonadResolver` code so that we may eventually feed it to
`infer`, we opt for a simpler approach: when typechecking an expression \\(e\\) within an environment
\\(x_1:\\tau_1, \\ldots, x_n:\\tau_n\\), we convert it into an expression \\(\\lambda (x_1:\\tau_1).\\ldots\\lambda (x_n:\\tau_n). e\\),
and perform typechecking in an empty environment. That way, `infer` handles extending the environment (also
ensuring the environment's validity as usual), sparing us the otherwise necessary duplication of code.

> elaborateInEnv :: MonadResolver m => Maybe (S.Term, S.Term) -> [ResolveTerm] -> ResolveTerm -> m ([S.Term], S.Term)
> elaborateInEnv mtd env t = inferWithin $ do
>     let mtt = snd <$> mtd
>     let mt = fst <$> mtd
>     self <- mkMSelf mtt
>     ienv <- mapM (instantiate self) env
>     it <- instantiate self t
>     infer $ foldr S.Abs it ienv
>     let stripBody = strip (length env) 
>     let stripEnv = zipWithM strip [0..]
>     case (mt, self) of
>         (Just t', Just k) -> liftA2 (,) (stripEnv $ map (subst k t') ienv) (stripBody $ subst k t' it)
>         _ -> liftA2 (,) (stripEnv ienv) (stripBody it)

At the very top of `elaborateInEnv` is a call to `inferWithin`. Thus little function
allows us to "switch contexts", and perform operations in a type inference monad instead
of a resolution monad. The underlying implementation is simple: we run the inference monad
and convert the error into a `MonadResolver`-compatible type.

> inferWithin :: MonadResolver m => InferU String a -> m a
> inferWithin m = liftEither $ first InferError $ runInferU m 

The rest of the elaboration functions use `elaborateInEnv` in a variety of ways. The simplest
case is elaborating something like the type of a function, which cannot have a recursive referene
to the function itself, and which does not occur inside any environment. We call this case
`elaboratePlain`.

> elaboratePlain :: MonadResolver m => ResolveTerm -> m S.Term
> elaboratePlain t = snd <$> elaborateInEnv Nothing [] t

A more interesting case is the elaboration of the parameters and indices
of an inductive data type. This is where having our environment as a list of `ResolveTerm`s
comes in handy: we make a call to `elaborateInEnv` and simply ask it to resolve the expresion
`S.Sort Prop` (which clearly does not need to be resolved, since it has no placeholders and no
self-references). By doing so with an environment made up of parameters an indices, though, we
wrangle `infer` into typechecking each parameter and index in turn, each time extending the environment
with the resulting type so that the subsequent parameters and indics (which, in the general
case, can depend on it) also typecheck correctly. Of course, we don't care for the result
of elaborating `S.Sort Prop`; we merely throw it away, and return only the elaborated parameters
and indices.

> elaborateInd :: MonadResolver m => [ResolveTerm] -> m [S.Term]
> elaborateInd pis = fst <$> elaborateInEnv Nothing pis (S.Sort Prop)

When elaborating a function, we make use of `selfFunction` to require that we are,
indeed, within a function, and to retrieve the function's type and a reference
to the function's future term (`cdType cd` and `cdFutureTerm`, respectively).
We then elaborate the function's body, extending the environment with the types of
the function's arguments, as explained above.

> elaborateFun :: MonadResolver m => ResolveTerm -> m S.Term
> elaborateFun bt = do
>     (cd, cf) <- selfFunction
>     (_, ebt) <- elaborateInEnv (Just (cdFutureTerm cd, cdType cd)) (parameterizeAll $ cfParams cf) bt
>     return ebt

Constructors seem to always require a bit more hassle. First and foremost, constructors
can reference their own data type, which we treat as a `SelfRef`. For this reason, we
require that the "current inductive type" is present, retrieving it via `selfInductive`.
A constructor is parameterized by both the inductive type's parameters (for instance,
the `a` from `List a` is available to `Cons` and `Nil`) and its own parameters. These
are all present when elaborating its result type (and the constructor's parameter
types themselves need to be elaborated themselves). We store this combined list
of parameters into `allPs`.

A
{{< sidenote "left" "data-constructor-note" "(data) constructor" >}}
Like <code>Nil</code>, <code>Cons</code>, <code>Left</code> or <code>Right</code> for example.
{{< /sidenote >}}
always implicitly applies its
{{< sidenote "right" "type-constructor-note" "(type) constructor">}}
The <em>type</em> constructors for the <em>data constructors</em> listed
previously are <code>List</code> and <code>Either</code>.
{{< /sidenote >}}
to the inductive data type parameters. For instance, in the case of list `List a`, `Cons` will always return `List a`,
and not `List b`. Similarly, the type constructors `Left` and `Right` of an `Either` data type, which accepts
two type parameters, `A` and `B`,
{{< sidenote "left" "index-note" "will always produce" >}}
Note that this is only the case for <em>parameters</em>, which are shared
between all constructors. Indices are not automatically filled in, and each (data) constructor
can specify the indices it feeds as parameters to its (type) constructor. This is how we can
have GADTs.<br>
For example, we can have a vector <code>Nil</code> constructor return <code>Vec A O</code>,
while <code>Cons</code> would return <code>Vec A (S n)</code> for some natural number <code>n</code>.
{{< /sidenote >}}
`Either A B`.  We thus generated references to these parameters by simply generating the sequence
\\(n+k,\\ldots,1+k,k\\), where \\(n\\) is the number of inductive parameters, and \\(k\\) is the number
of the constructor's own parameters, which are _not_ automatically applied, and simply cause an
offset to the DeBrujin indices we need. This sequence is stored in `paramRefs`. Finally,
we assemble the whole type to be elaborated and feed it through `elaborateInEnv`. We have
to perform a bit of a hacky trick here: we want to retrieve the results of elaborating the indices
of the constructor, but those have been fused into a series of type constructor applications.
We thus use the `collectApps` function from our `Checking` module, which extracts the arguments
applied to some inductive data type. This isn't quite ideal because we know that an error is impossible
here: we just assembled a valid application, and should thus get a valid application back. However,
`collectApps` does not know about this, and we must add code to handle impossible errors.

When returning from the constructor application, we drop the inductive data type's parameters
from everywhere: they have already been elaborated elsewhere.

> elaborateCon :: MonadResolver m => [ResolveTerm] -> [ResolveTerm] -> m ([S.Term], [S.Term])
> elaborateCon ps is = do
>     (cd, ci) <- selfInductive
>     let ips = ciParams ci
>     let allPs = parameterizeAll ips ++ ps
>     let paramRefs = map (S.Ref . (+ length ps)) $ reverse [0..length ips -1]
>     let ret = foldl S.App (S.Param SelfRef) (paramRefs ++ is)
>     (eps, eret) <- elaborateInEnv (Just (cdFutureTerm cd, cdType cd)) allPs ret
>     (_, eretas) <- liftEither $ first (const InvalidResolve) $ collectApps eret
>     return (drop (length ips) eps, drop (length ips) eretas)

That's all for the various elaboration functions. Next for some bookkeeping!
As we saw above, we use a state monad to keep track of the decreasing arguments
of our potentially recursive functions. Each time we resolve a function, we
must be careful to start fresh, without accidentally assuming that
the decreasing parameters of the _previous_ function match that of the current
one. For this reason, we write a little helper to perform a monadic
operation in a state with no recorded decreasing arguments, which
we can conveniently use to get a "blank slate".

> withNoDecreasing :: MonadState ResolveState m => m a -> m a
> withNoDecreasing m = do
>     dec <- gets rsDecreasing
>     modify $ \rs -> rs { rsDecreasing = Nothing }
>     a <- m
>     modify $ \rs -> rs { rsDecreasing = dec }
>     return a

Now, we finally get to recording the decreasing arguments of a function.
There are two possible situations:

* `rsDecreasing` is `Nothing`. This means that until now, there have
  been no recursive calls, and we have had no need to record decreasing
  arguments. In this case, the given set of potential candidates for
  the decreasing argument becomes the current set.
* `rsDecreasing` is `Just s'`, an existing set of decreasing arguments.
  We then intersect `s` with `s'`, since only arguments that are in
  both of those lists can still be candidates (a decreasing argument
  is always decreasing, not just sometimes).

{{< todo >}}
This is just the monoid instance for Maybe with Set's intersection
as the underlying semigroup. That means, this code can be way more
concise.
{{< /todo >}}

> recordDecreasing :: MonadState ResolveState m => Set.Set String -> m ()
> recordDecreasing s = modify $ \rs -> rs { rsDecreasing = updateDec (rsDecreasing rs) }
>     where
>         updateDec Nothing = Just s
>         updateDec (Just s') = Just $ Set.intersection s s'

Building on `recordDecreasing`, we define `recordFixpoint`, which
looks into the environment, ensures that we are currently
within _some_ definition, and, if this definition is
a function, retrieves the current applications that are
"decreasing" from `reApps`, and records them with `recordDecreasing`.

> recordFixpoint :: MonadResolver m => m ()
> recordFixpoint =
>     do
>         asks reCurrentDef
>             >>= maybe (throwError InvalidFixpoint) return
>             >>= either (const $ return ()) (record . cfParsed) . cdExtra
>     where
>         record cf = do
>             params <- take (length $ pfArity cf) <$> asks reApps
>             smallerParams <- smallerParams <$> mapM termSize params
>             recordDecreasing smallerParams

For the above function, we use two little helpers. The first is a function `termSize`,
which, unsurprisingly, returns the "size" of a particular term. For now, we
only allow references to have sizes, and treat other terms as "incomparable"
(and thus, never decreasing).

> termSize :: MonadResolver m => ParseTerm -> m (Maybe (String, VarSize))
> termSize (Ref (StrRef s)) = Just . (,) s <$> varSize s
> termSize _ = return Nothing

The second is called `smallerParams`; it is given a list of term sizes produced
by `termSize`, and converts this list into a set of original parameter names
that "decreased".

> smallerParams :: [Maybe (String, VarSize)] -> Set.Set String
> smallerParams mps = Set.fromList $ catMaybes $ map (>>=(varParent . snd)) mps

Aside from emitting decreasing arguments, we will also emit exports
that are produced within this module, to be added to the current
scope and made available from subsequent definitions.

> emitExport :: MonadResolver m => String -> ExportVariant -> m ()
> emitExport s ev = do
>     mn <- currentModule
>     let export = Export ev mn
>     let nQual = Map.singleton (qualName mn s) export
>     let nUnqual = Map.singleton (unqualName s) [export]
>     let ngs = GlobalScope nQual nUnqual
>     gs' <- gets ((`mergeScopes` ngs) . rsScope) >>= (liftEither . first ImportError)
>     modify $ \rs -> rs { rsScope = gs' }

We can also define small helper functions that automatically
wrap inductive definitions or functions in their appropriate `Export`
constructor, and emit them. Here's one for functions:

> emitInd :: MonadResolver m => String -> Inductive -> m ()
> emitInd s i = emitExport s (IndExport i)

And here's one for inductive data types, which is almost identical.

> emitFun :: MonadResolver m => String -> Function -> m ()
> emitFun s f = emitExport s (FunExport f)

Finally, here's a slightly more involved one for constructors.
This one actually calls `emitExport` several times, once for
each constructor.

> emitConstructors :: MonadResolver m => Inductive -> m ()
> emitConstructors i = zipWithM_ emitConstructor [0..] (iConstructors i)
>     where emitConstructor ci c = emitExport (cName c) (ConExport i ci)

Despite the similar name, `emitDef` has a different
purpose compared to the previous handful of functions. Whereas
`emitExport`, `emitInd`, and `emitFun` augment the current
scope with the newly emitted definitions, recall (from the `Modules` module),
that such a `GlobalScope` is _computed_ from a `Module` when it is imported.
A `GlobalScope` contains _all_ definitions available to code in a module,
including those imported from elsewhere. Of course, we don't want to
re-compute a `GlobalScope` every time, so modifying one with new exports
makes sense. However, we also need to maintain a "clean" copy, a `Module`
instance, which contains the visibilities / access modifiers of each
definition from only the current module. The task of `emitDef` is to
update this instance (specifically, the mapping of names to `Definition` instances).

> emitDef :: MonadResolver m => String -> Definition -> m ()
> emitDef s d = modify $ \rs -> rs { rsDefs = Map.insert s d $ rsDefs rs }

Next, we'll move a bit further into the process of resolution. Our next
function, `insertLeading`, will take a list of parameter types (which
can be either `Inferred` or `Explicit`, with `Inferred` parameters being
guessed using unification and) and insert the appropriate number of
`Placeholder` instances, which will eventually be processed by the
elaboration code. For now, we only handle the case of _leading_
inferred arguments (that is, placeholders can only occur at the
beginning of a call, and not in the middle).

> insertLeading :: [ParamType] -> ResolveTerm -> ResolveTerm
> insertLeading ps t = foldl S.App t $ replicate (length $ takeWhile (==Inferred) ps) (S.Param Placeholder)

We then use `insertLeading` in the implementation of `exportToTerm`.
For the time being, we only do this with occurences of functions,
and not type- or data-constructors.

> exportToTerm :: Export -> ResolveTerm
> exportToTerm e = case eVariant e of
>     FunExport f -> insertLeading (map snd $ fArity f) (S.Fun f)
>     ConExport i ci -> S.Constr i ci
>     IndExport i -> S.Ind i

While we're messing with `ParamType`s, let's also define a function
to retrieve the current definition's parameter types. In agreement
with our `exportToTerm` function, we only allow functions' implicit
arguments to be turned into placeholders (for the time being). 

> currentParamTypes :: MonadResolver m => m (Maybe [ParamType])
> currentParamTypes = do
>     mcd <- asks reCurrentDef
>     return $ case cdExtra <$> mcd of
>         Just (Right cf) -> Just $ pfParamTypes $ cfParsed cf
>         Just Left{} -> Nothing

We're finally getting closer to actually processing syntax trees.
One particular scenario that we need to handle is the resolution
of an unqualified name, like "length". It's possible that two things
with the unqualified name "length" are present in current scope:
maybe the length functions on lists and vectors. Thus, we look up
the appropriate name in the `sUnqualified` field of our scope (`rsScope`),
and hand it off to a helper function `narrowExports`.
 
> lookupUnqual :: MonadResolver m => String -> m ResolveTerm
> lookupUnqual s = do
>     es <- gets (fromMaybe [] . Map.lookup (unqualName s) . sUnqualified . rsScope)
>     exportToTerm <$> narrowExports es

This little helper function implements the expected behavior for resolving
a variable reference: if there is no known export with the given name,
we have an `UnknownReference`; if there is more than one export with
the given name, the reference is ambiguous. Only when the name corresponds
to exactly one export do we successfully return it.

> narrowExports :: MonadResolver m => [Export] -> m Export
> narrowExports [] = throwError UnknownReference
> narrowExports [x] = return x
> narrowExports _ = throwError AmbiguousReference

The qualified lookup function is simpler, since we do not
allow two exports to occupy the same qualified name. Thus,
we simply perform a lookup, and we're basically done.

> lookupQual :: MonadResolver m => Symbol -> m ResolveTerm
> lookupQual s = do
>     me <- gets (Map.lookup s . sQualified . rsScope)
>     maybe (throwError UnknownReference) (return . exportToTerm) me

The two functions, `lookupUnqual` and `lookupQual`, are combined
into a `lookupRef` function, which decides which lookup to
perform depending on whether the given reference is a symbol
(a qualified name) or a string (an unqualified name).

> lookupRef :: MonadResolver m => ParseRef -> m ResolveTerm
> lookupRef (SymRef s) = lookupQual s
> lookupRef (StrRef s) = lookupUnqual s

The next function, `lookupInd`, is just a wrapper of `lookupRef`
that only succeeds if the export we found is an inductive data type.

> lookupInd :: MonadResolver m => ParseRef -> m S.Inductive
> lookupInd r = do
>     t <- lookupRef r
>     case t of
>         S.Ind i -> return i
>         _ -> throwError NotInductive

We're gradually building up to resolving more and more complicated
parts of our abstract syntax tree. Next up is `resolveIndRef`, which
converts a `ParseIndRef` (a tuple of a reference and a list of strings,
representing most generally the expression `M1.M2.T x y z`), which is
used in the `return` portion of case expressions, into a tuple of the given
inductive type and the list of strings. This function additionally checks
that the `ParseIndRef` is valid: that is, we're not writing something like
`Either A` where the valid equivalent would be `Either A B`.

> resolveIndRef :: MonadResolver m => ParseIndRef -> m (S.Inductive, [String])
> resolveIndRef (r, is) = do
>     i <- lookupInd r
>     if length (iArity i) == length is
>      then return (i, is)
>      else throwError InvalidArity

Continuing with the case expression motif, we have `resolveBranch`, which introduces
the variables from a case expression branch into the scope, and tries to resolve
the branch's expression. For convenience, it also returns the constructor name
that was used in the branch.

> resolveBranch :: MonadResolver m => VarSize -> ParseBranch -> m (String, ResolveTerm)
> resolveBranch vs (s, ps, t) = (,) s <$> withSizedVars vs ps (resolveTerm t)

Given a list of the `(constructor name, term)` pairs produced by `resolveBranch`, we define
a function `matchBranch` to find a `ResolveTerm` for a particular `Constructor`.

> matchBranch :: MonadResolver m => [(String, ResolveTerm)] -> Constructor -> m ResolveTerm
> matchBranch bs c = maybe (throwError IncompleteMatch) return $ lookup (cName c) bs 

When do variables actually decrease in size? In Maypop, this will happen
during pattern matching. If a reference `l` is case analyzed into
a head `x` and tail `xs`, then `x` and `xs` are smaller than `l`,
since they make up parts of l. This logic is implemented by
`caseTermSize`, which, given a term that occurs as a scrutinee
of a case expression, returns the `VarSize` that should be assigned
to each variable introduced by the case expression's patterns.

> caseTermSize :: MonadResolver m => ParseTerm -> m VarSize
> caseTermSize t = do
>     mts <- termSize t
>     return $ case mts of
>         Just (s, Original) -> SmallerThan s
>         Just (_, vs@SmallerThan{}) -> vs
>         _ -> Unknown

Finally, we reach one of the major functions in this module:
resolving terms. Most of the rules are "structural", assembling
resolved terms by resolving their sub-terms. At most, there's
some bookkeeping (tracking applications via `withApp` and `clearApps`,
introducing variable names via `withVar`). We'll list
these "boring" cases first.

> resolveTerm :: MonadResolver m => ParseTerm -> m ResolveTerm
> resolveTerm (Ref (SymRef s)) = lookupQual s
> resolveTerm (Abs (x, tt) t) = clearApps $ liftA2 S.Abs (resolveTerm tt) (withVar x $ resolveTerm t)
> resolveTerm (App l r) = liftA2 S.App (withApp r $ resolveTerm l) (resolveTerm r)
> resolveTerm (Let (x, t) ti) = liftA2 S.Let (clearApps $ resolveTerm t) (withVar x $ resolveTerm ti)
> resolveTerm (Prod (x, tt) t) = clearApps $ liftA2 S.Prod (resolveTerm tt) (withVar x $ resolveTerm t)
> resolveTerm (Sort s) = return $ S.Sort s

The first interesting case is that of a unqualified reference. 
The case is interesting because this is precisely the place where
our fixpoint detection will occur (the same is not true for the fully
qualified case, since the function is not yet placed into the global
scope, and thus is not listed under a fully qualified name). Recall that the
`lookupVar` function may return to us `Left ()`, indicating that we
encountered a reference to `Self`, `Right i`, returning to use the DeBrujin
index `i` of the variable `s`, or `Nothing`, letting us know that
the current name is not part of the "local" scope, and must be a definition
from the `GlobalScope`. In the `Left ()` case, we first call `recordFixpoint`,
storing the arguments to the recursive call that we found to decrease. In
the last two lines of this case, we retrieve the list of `ParamType`s
of the current function, and use it to insert placeholders as necessary
via `insertLeading`. The other two cases require little further explanation.

> resolveTerm (Ref (StrRef s)) = do
>     vref <- lookupVar s
>     case vref of
>         Just Left{} -> do
>             recordFixpoint
>             pts <- currentParamTypes
>             return $ insertLeading (fromMaybe [] pts) (S.Param SelfRef)
>         Just (Right i) -> return $ (S.Ref i)
>         Nothing -> lookupUnqual s

The second interesting case is that of case expressions. Here, we still
perform resolution on subterms, but a little more setup is necessary:
we need to determine whether or not we have to mark the newly introduced
variables with a size. This is where our `resolveBranch` and matchBranch`
functions come in: the former is used to process each branch in turn,
and they are arranged in proper order by calling `matchBranch` for
every constructor.

> resolveTerm e@(Case t x ir tt bs) = clearApps $ do
>     t' <- resolveTerm t
>     vs <- caseTermSize t
>     (i, is) <- resolveIndRef ir
>     tt' <- withVars (x:is) $ resolveTerm tt
>     bs' <- mapM (resolveBranch vs) bs
>     cbs <- mapM (matchBranch bs') $ iConstructors i
>     return $ S.Case t' i tt' cbs

That's it for terms! What remains is to resolve the various
function and inductive data type definitions. We can start
with functions. The process here is fairly straightforward:

* We elaborate the function's type. This returns us a single
  term, like `Nat -> Nat -> Nat` in the case of a function like `plus`.
* We then pick off the types of the function parameters. For instance,
  if the function was defined as `plus x y = ...`, we'd pick off
  the two `Nat`s (one for `x` and one for `y`), and leave a single
  `Nat` behind.
* We then set up the environment for resolving and elaborating the
  function's body. Here we use `rec f' <-`, which is a bit of special
  syntax from `MonadFix` that makes `f'` available on the right hand
  side of the `do`-notation arrow as a handle on the computation's future
  result. We use `withNoDecreasing` to clear the set of decreasing arguments,
  and `withFunction` to add the current function's type, future term, etc.
  to the environment.
* Next, we resolve the function's body. While doing so,
  our code called `recordFixpoint` for every recursive occurence,
  so we're ready to read that information. We do so with `findDecreasing`,
  which provides us the last piece of information required to create a `Function`.
  We return what we create.
* Finally, we `emitFun` to add our new function to the global scope, and
  `return` our result.

> resolveFun :: MonadResolver m => ParseFun -> m Function
> resolveFun f = do
>     fts <- resolveTerm (pfType f) >>= elaboratePlain
>     (ats, rt) <- liftEither $ collectFunArgs (pfParamNames f) fts
>     rec f' <- withNoDecreasing $ withFunction (S.Fun f') fts ats f $ do
>          fb <- resolveTerm (pfBody f) >>= elaborateFun
>          dec <- findDecreasing (pfParamNames f)
>          return $ Function (pfName f) (zip ats (pfParamTypes f)) rt fb dec
>     emitFun (pfName f) f'
>     return f'

As usual, we used helper functions in the above definition. The first helper
function is `findDecreasing`; it retrieves the now-accurate
set of decreasing arguments from the state, and converts it into indices
of the function's parameters (we do not use names in our final representation).
Three cases are possible.

1. We are not a recursive function. In this case, `dec` is `Nothing`,
   and we simply return `Nothing`. A `Maybe` in a function's decreasing
   parameter field tells Maypop to use regular old beta reduction when
   evaluating it.
2. We are a recursive function, and at least one argument is always
   decreasing. We return the index of this argument wrapped in `Just`,
   indicating that our function is recursive and decreasing on the `x`th
   argument.
3. We are a recursive function, but no argument is reliably decreasing.
   This is an error, which we report as `InvalidFixpoint`.

> findDecreasing :: MonadResolver m => [String] -> m (Maybe Int)
> findDecreasing args = do
>     dec <- fmap (decreasingIndices args . Set.toList) <$> gets rsDecreasing
>     case dec of
>         Just (x:_) -> return $ Just x
>         Just [] -> throwError InvalidFixpoint
>         _ -> return Nothing

The `findDecreasing` helper itself uses a helper, `decreasingIndices`.
This function simply maps decreasing arguments to their indices in
the list of all of the function's parameters.

> decreasingIndices :: [String] -> [String] -> [Int]
> decreasingIndices args dec = sort $ catMaybes $ map (`elemIndex` args) dec

The second helper used by `resolveFun` is `collectFunArgs`, which is used to
turn a single function term (like the `Nat -> Nat -> Nat` example above) into
a list of parameter types and a return type. The implementation simply "picks off"
instances of the `Prod` constructor.

> collectFunArgs :: [String] -> (S.ParamTerm a) -> Either ResolveError ([S.ParamTerm a], S.ParamTerm a)
> collectFunArgs [] t = return $ ([], t)
> collectFunArgs (_:xs) (S.Prod l r) = first (l:) <$> collectFunArgs xs r
> collectFunArgs _ _ = throwError InvalidArity

That's all for function definitions. Let's move on to inductive definitions!
Some amount of mechanical manipulation is required in this function's
implementation, but its general structure is fairly similar to
that of `resolveFun`:

* We resolve the inductive data type's type. This is similar
  to what we did with the function definition's type, except
  that in data type definitions we're already _given_ separate
  parameter, index, and return types. Our task of resolving
  them becomes that much more difficult, though: each parameter
  introduces a new name, on which subsequent parameters may
  possibly depend. To resolve a list of parameters, we have to
  use a special helper, `resolveParams`.
* Since we need the inductive data type's type, we reassmble the indices
  and parameters into `it`.
* Now knowing the type of the inductive data type, we prepare to
  typecheck each of the constructors. We once again use
  the `rec` notation from `MonadFix` to get a handle on our
  future inductive type, and call `withInductive` (not bothering
  to use `withNoDecreasing`).
* Next, we actually resolve each of the constructors. This is handled
  by `resolveConstr`, which we will look at shortly.
* Now finished with the resolution, we emit the inductive
  data type and its constructors (placing them into the global scope),
  and `return`.

> resolveInd :: MonadResolver m => ParseInd -> m S.Inductive
> resolveInd pi = do
>     its <- resolveParams (piAllParams pi ++ piArity pi) >>= elaborateInd
>     let it = foldr S.Prod (S.Sort $ piSort pi) its
>     let (ps', is') = splitAt (length $ piParams pi) its
>     rec i' <- withInductive (S.Ind i') it ps' is' pi $ do
>          cs <- mapM resolveConstr (piConstructors pi)
>          return $ Inductive (zip ps' (piParamTypes pi)) is' (piSort pi) cs (piName pi)
>     emitInd (piName pi) i' 
>     emitConstructors i'
>     return i'

This time, constructors don't appear to be too much of a hassle. We
use the same `resolveParams` helper as we did in `resolveInd` to get
a list of the constructor's parameters, and then separately resolve
the constructor's indices in the environment extended with the names
of the constructor's parameters. The last step is a call to elaboration,
and we are left with a valid `Constructor` instance.

> resolveConstr :: MonadResolver m => ParseConstr -> m S.Constructor
> resolveConstr pc = do
>     ps' <- resolveParams (pcAllParams pc)
>     is' <- withVars (pcParamNames pc) $ mapM resolveTerm (pcIndices pc)
>     (ps'', is'') <- elaborateCon ps' is'
>     return $ Constructor (zip ps'' (pcParamTypes pc)) is'' (pcName pc)

The actual implementation of the `resolveParams` helper is actually quite simple.
For each named term in the list, we resolve the term, and then resolve the remaining
terms in an environment extended with the term's name. This happens recursively,
so for \\(x_1:\\tau_1, x_2:\\tau_2, x_3:\\tau_3\\), \\(x_1\\) is resolved
by itself, \\(x_2\\) is resolved in an environment containing \\(x_1\\),
and \\(x_3\\) is resolved with awareness of both \\(x_1\\) and \\(x_2\\).

> resolveParams :: MonadResolver m => [ParseParam] -> m [ResolveTerm]
> resolveParams = foldr (\(x, t) m -> liftA2 (:) (resolveTerm t) (withVar x m)) (return [])

Now able to resolve both function definitions and inductive definitions,
we write a function to resolve a `ParseDef` into a `Definition`. It is
in this function that we use `emitDef`, and thus update the part of the
`Module` data structure that we are currently in the process of constructing.

> resolveDef :: MonadResolver m => ParseDef -> m Definition
> resolveDef d = do
>     dc <- either (fmap IndDef . resolveInd) (fmap FunDef . resolveFun) d
>     let def = Definition Public dc
>     emitDef (dName def) def
>     return def

Finally, we tie all this together in `resolveDefs`. This function receives
an already-parsed module header, a `GlobalScope` containing the definitions
from all of the module's imports, and a mapping of strings to parsed
definitoins that need to be resolved. It may, of course, fail, but if it suceeds,
it returns a map of definition names to their implementations, which will
become part of the `Module` record.

> resolveDefs :: ModuleHeader -> GlobalScope -> [(String, ParseDef)] -> Either ResolveError (Map.Map String Definition)
> resolveDefs mh gs ps = (rsDefs . snd) <$> (runExcept $ runReaderT (runStateT (mapM (resolveDef . snd) ps) state) env)
>     where
>         env = ResolveEnv { reVars = [], reHeader = mh, reCurrentDef = Nothing, reApps = [] }
>         state = ResolveState { rsScope = gs, rsDefs = Map.empty, rsDecreasing = Nothing }
