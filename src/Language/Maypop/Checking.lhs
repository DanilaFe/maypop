Let's work on type inference a little.

> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE MonoLocalBinds #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> module Language.Maypop.Checking where
> import Language.Maypop.Syntax
> import Language.Maypop.Eval
> import Language.Maypop.Modules
> import Language.Maypop.Context
> import Language.Maypop.InfiniteList
> import Language.Maypop.Unification hiding (substitute)
> import Control.Monad.Reader
> import Control.Monad.Except
> import Control.Applicative
> import Data.Bifunctor
> import Data.Bool
> import Data.Void
> import Data.Maybe
> import qualified Data.Map as Map

{{< todo >}}Explain the names in the environment.{{< /todo >}}

First, a little utility function to compute the type of a type. This
is straight out of the paper on the Calculus of Inductive Constructions.
Prop has the type \\(\\text{Type}_0\\), and each type \\(\\text{Type}\_n\\) has type \\(\\text{Type}\_{n+1}\\).

> nextSort :: Sort -> Sort
> nextSort Prop = Type 0
> nextSort (Type i) = Type $ i+1

Type inference can fail, so let's define a type for any kind of error that can
come up.

> data TypeError
>     = FreeVariable Int
>     | NotSort
>     | NotProduct
>     | NotInductive
>     | TypeError
>     | TypeMismatch Term Term
>     | UnknownConstructor
>     deriving Show

Our implementation of unification and `MonadUnify` relies on `MonadPlus`.
However, our usual error reporting mechanism is `MonadError`, specifically
`ErrorT`. These two aren't effortlessly compatible; however, there _does_
exist a `MonadPlus` instance for `ErrrorT`, when the type of errors
is a `Monoid`. We thus declare the following two (law-violating) instances:

> instance Semigroup TypeError where
>     l <> _ = l
>
> instance Monoid TypeError where
>     mempty = TypeError

It is also helpful to write a function that ensures a boolean condition
is met, failing if it isn't. Aside from the condition, we need to
provide information about what actually went wrong, in the form
of a `TypeError`:

> guardE :: MonadError te m => te -> Bool -> m ()
> guardE e = bool (throwError e) (return ())

All of these `Monad` constraints that we keep sticking onto our functions
are going to start seeming repetitive. Instead of dealing with that, we
can define a trivial type class instance, `MonadInfer k`, which implies
all of the other common constraints. The `k` in this definition is the type
of parameters that our terms are parameterized by.

> class (Eq k, MonadReader [(String, ParamTerm k)] m, MonadError TypeError m, MonadUnify k (Context String k) m, MonadInf String m) => MonadInfer k m where
> instance (Eq k, MonadReader [(String, ParamTerm k)] m, MonadError TypeError m, MonadUnify k (Context String k) m, MonadInf String m) => MonadInfer k m where

> unifyTerms :: MonadInfer k m => ParamTerm k -> ParamTerm k -> m (ParamTerm k)
> unifyTerms t1 t2 = do { bs <- asks (map fst); unifyInContext bs t1 t2 }

> reifyTerm :: MonadInfer k m => ParamTerm k -> m (ParamTerm k)
> reifyTerm t = do 
>     bs <- asks (map fst)
>     ctxValue <$> reify (Context bs Nothing (Just t)) >>= maybe mzero return

Finally, on to the type inference function. We use the `MonadReader`
typeclass to require read-only access to the local environment \\(\\Gamma\\).
This function is so complicated that we should go through it case-by-case.

> infer :: MonadInfer k m => ParamTerm k -> m (ParamTerm k)

When we are inferring the type of a DeBrujin index, all we need
to do is look in the current context to see what the index
corresponds to. It's possible that the index corresponds to
nothing; in this case, we throw the `FreeVariable` type error.

> infer (Ref n) = nth n . map snd <$> ask >>= maybe (throwError (FreeVariable n)) return

The type of a function is simply its full type. This type is initially
a `Term`, but, since we're performing inference over potentially parameterized
terms, we need to call `parameterize`. The case for fixpoints is pretty much identical; the decreasing
argument is irrelevant to a function's type.

> infer (Fun f) = return $ parameterize $ fFullType f

The case for parameters must be present, but I'm not currently
sure what the best way of handling it is. For now, it remains
unimplemented.

> infer (Param p) = do
>     bs <- asks (map fst)
>     ctx <- bind p (Context bs Nothing Nothing)
>     case ctxType ctx of
>         Just t -> return t
>         Nothing -> do
>             t <- Param <$> fresh
>             bind p (Context bs (Just t) Nothing)
>             return t

The type of a lambda abstraction is a product type;
the first component of `Abs` is the input type,
so we include it directly. The return type must
be computed from the lambda abstraction body. Since
the argument to the lambda abstraction is also available
in the body, we must extend the environment with its type.
The `extend` helper function is defined below, and it ensures
the validity of `t` before adding it to the context.

> infer (Abs t b) = Prod t <$> extend t (infer b)

In the application case, we infer the types of both the left-
and right-hand side terms. We require the left term to
be a product type (we enforce this using the `inferP` helper).
Once the two types are computed, we compare (using unification)
the function's expected input type and the type of the argument,
and, if they match, return the function's return type. There's
a little trick here: the return type of the function may depend
on value of the argument, so we perform substitution to provide
it this value.

> infer (App f a) = do
>     (ta, tb) <- inferP f
>     targ <- infer a
>     unifyTerms (eval ta) (eval targ)
>     reifyTerm $ substitute 0 a tb

A let expression is not explicitly decorated with types; we thus
infer the type of newly introduced variable (in the `let` portion)
and then use it to extend the environment in which the returned
expression (the `in` portion) is typechecked.

> infer (Let l i) = infer l >>= flip extend (infer i)

The product rule is somewhat tricky because the exact type depends
on the sort of the return type. The `Prop` sort is impredicative,
which means that it can actually refer to itself, and to "higher level"
sorts like `Type 0`, `Type 1`, and so on. Thus, if the sort of
the return type is `Prop`, it's fine and dandy for us to type the
entire product type as `Prop`. However, `Type n` is predicative; it
can't refer to itself, and anything accepting values such as `Type 0`
{{< sidenote "right" "russel-note" "cannot itself be of sort" >}}
This aligns closely with Bertrand Russel's work, _Mathematical Logic as
Based on The Theory of Types_, where he writes: "Thus, whatever contains an
apparent variable must be of a different type from the possible values
of that variable; we will say that it is of a _higher_ type".
{{< /sidenote >}}`Type 0`, but something of at least sort `Type 1`.
We implement this as follows:

> infer (Prod a b) = extend' a $ \ua -> inferS b >>= \ub -> return $ Sort $
>     case ub of
>         Prop -> Prop
>         t -> joinS ua t

The type of a sort is simply the next largest sort. We use a helper
function `nextSort`, defined below, to simplify the code here.

> infer (Sort u) = return $ Sort $ nextSort u

A constructor of an inductive type `i` accepts not only its
own parameters, but also the parameters of the inductive data
type itself. Furthermore, its return type actually contains
the inductive data type's parameters. Thus, we have to
do quite a bit of bookkeeping.

The most complicated
part is the return type. It is at the end of a chain
of product types, with the first few product types serving to accept 
the inductive data type's parameters, and the subsequent few products
to accept the parameters of the constructor. The first
order of business is to re-iterate the inductive data type's
parameters in the return type. They are behind `length (cParams c)`
constructor parameters, and we thus compute their indices by adding
that number to `0`, `1`, and so on. This is done by `cParamRefs`
and `cIndParams`. The remaining arguments to the `Inductive` type
constructor are the indices of the particular construtor (`cIndices c`),
which require no further wrangling.

Having thus computed the return type, we place it at the end of a chain
of products (as promised) with a straightforward right fold. Tying this
all together, we handle the potential for an invalid constructor reference
(with an invalid constructor index `ci`) using `withConstr` and `mConstr`.

> infer (Constr i ci) = withConstr $
>     \c -> return $ parameterize $ foldr Prod (cReturn c) (iParams i ++ cParams c)
>     where
>         mConstr = nth ci $ iConstructors i
>         withConstr f = maybe (throwError UnknownConstructor) f mConstr
>         cParamRefs c = map (+length (cParams c)) [0..length (iParams i) -1]
>         cIndParams c = map Ref $ reverse $ cParamRefs c
>         cReturn c = foldl App (Ind i) $ cIndParams c ++ cIndices c

Things are much simpler for an inductive data type itself; it's a type
constructor returning its sort (`iSort i`), taking as arguments its
parameters and indices.

> infer (Ind i) = return $ parameterize $ foldr Prod (Sort $ iSort i) $ iParams i ++ iArity i

Probably the most complicated case is that of a `Case` expression. In the
code, the upser specifies the expected return type (`tt`), which may
contain references to the expression being anayzed and any of its
indices. We have to validate that this is a well-formed type,
but also that each branch's type matches up with `tt`. First
things first, we compute the actual type of the _scrutinee_ (the expression
being analyzed), and ensure that its type is what is expected. We
then extract the parameters and indices of the scrutinee's type.

The data type's parameters can themselves occur in the types
of each constructor's parameters. Since we know their values,
we can substitute them into anywhere they are needed. For this,
we define a function `subPs`, which, given an offset (the number
of binders between the parameters and the term where substituion
is occuring), substitute the parameters in.

We move on to handling constructors. The types of the constructor
parameters are augmented (via substitution) by the types of
the data type's parameters, producing `cps`. The same is
done with the constructor's indices, producing `inds'`.
When specializing `tt` for each constructor, the return
type can contain references to the scrutinee, which is now
known to be a constructor with some parameters. The parameters
themselves are not known, but nor are their types in the
type environment when checking `tt`. We thus introduce "dummy",
negative references (`-1`, `-2`, and so on) to represent these
parameters. This is done by `rcps`, and our scrutinee expression
is saved into `expt`. Finally, we instantiate `tt` with the
index types and the "concrete" scrutinee, and compare
the inferred type of the branch to the new `tt`.

And that's the constructor code in `constr`. We finally check the
`tt` in the "general case", by extendign the environment with the
types of the indices (from `ar`), as well as the type of the scrutinee
(`tType`). Having validated this type, we actually run `constr` on
each branch, and return the case expression's final type.

> infer (Case t i tt ts) = do
>     (i', is) <- inferI t
>     guardE TypeError $ i == i'
>     let (ps, inds) = splitAt (length $ iParams i) is
>     let subPs off = substituteMany off (map (offsetFree off) ps)
>     let tType = foldl App (Ind i) is
>     let constr (ci,c) b = do
>          let cps = zipWith subPs [0..] $ parameterizeAll $ cParams c
>          let inds' = map (subPs $ length cps) $ parameterizeAll $ cIndices c
>          let rcps = map (Ref . negate) $ [1..length cps]
>          let expt = foldl App (Constr i ci) $ rcps
>          let et = substituteMany 0 (expt:inds') tt
>          at <- substituteMany 0 rcps <$> (extendAll cps $ infer b)
>          unifyTerms (eval at) (eval et)
>     let ar = zipWith (\n -> offsetFree 1 . subPs n) [0..] $ parameterizeAll $ iArity i
>     extendAll (tType: ar) $ inferS tt
>     zipWithM constr (zip [0..] $ iConstructors i) ts
>     return $ substituteMany 0 (t:inds) tt

And that's it! We've made it through the type inference code. There
are still helper functions remaining for us to implement. For instance,
this code that we've written is polymorphic over some `MonadInfer m`,
but when we actually run the code, we want some _particular_ `m`!
For now, we leave actual unification aside, and use a specialized
`UnifyEqT` monad transformer that operates on non-parameterized terms.
In this case, unification is reduced to a trivial equality comparison,
and we're effectively just perfoming type checking. The entire
monad transformer stack for `MonadInfer Void` (the inference monad
for non-parameterized expressions) is as follows:

> type InferE a = UnifyEqT (Context String Void) (ExceptT TypeError (InfT String (Reader [(String, Term)]))) a

We can add a function to actually run an instance of this monad,
potentially failing with a `TypeError`:

> runInferE :: InferE a -> Either TypeError a
> runInferE m = runReader (runInfT (runExceptT $ runUnifyEqT m)) []

We also write a function to specifically run
our `infer`, which is special case of `runInferE`.

> runInfer :: Term -> Either TypeError Term
> runInfer = runInferE . infer

> type InferU k a = UnifyT k (Context String k) (ExceptT TypeError (InfT String (Reader [(String, ParamTerm k)]))) a
>
> runInferU :: (Eq k, Infinite k) => InferU k a -> Either TypeError a
> runInferU m = runReader (runInfT (runExceptT $ runUnifyT m)) []

Our definition of `infer` contains a few utility functions in the; let's take a look
at all of them in turn. First up is the family of `infer*` functions, which
not only perform inference, but also constraint the resulting type to be
_something_, like a product type. First up is `inferS`. We need this function because
not all terms consitute valid types. For instance, a lambda function is _not_ a
type, but it is a term. Indeed, computation aside, only the `Sort` constructor corresponds
to a valid type. However, some constructs in the Calculus of Constructions specifically require types,
such as \\(\\Pi\\). Thus, we'll define a way to "cast" a term into a valid sort. This will
be used to discard terms such as \\(\\Pi(\\lambda \\text{Prop}.0),\\text{Prop}\\), which have non-types in a
place where a type is needed.

> intoSort :: MonadError TypeError m => ParamTerm k -> m Sort
> intoSort (Sort u) = return u
> intoSort _ = throwError NotSort

We can use this to define a specialized version of `infer`:

> inferS :: MonadInfer k m => ParamTerm k -> m Sort
> inferS t = eval <$> infer t >>= intoSort

A similar casting function to `intoSort` is `intoProduct`, which helps
us require that a term is a dependent product (this is used for the application rule).
We return the two terms composing a product type rather than returning a `Term`, which
helps the type system "remember" that this is not just any term that passed our inspection.

> intoProduct :: MonadError TypeError m => ParamTerm k -> m (ParamTerm k, ParamTerm k)
> intoProduct (Prod a b) = return (a, b)
> intoProduct _ = throwError NotProduct

Once again, we define a specailized version of `infer` for products:

> inferP :: MonadInfer k m => ParamTerm k -> m (ParamTerm k, ParamTerm k)
> inferP t =
>     do
>         t' <- eval <$> infer t
>         -- This is a hack to make Void type inference work.
>         intoProduct t' <|> (freshProd >>= unifyTerms t' >>= intoProduct)
>     where freshProd = liftA2 Prod (Param <$> fresh) (Param <$> fresh)

Just as we may want to cast a data type into a product, we may also want to cast
it into an inductive data type, extracting the parameters and indices. Things
are a little trickier here, since fully applied inductive type constructors
are represented as a chain of `App` nodes. We thus define a function to turn this
tree into a list:

> collectApps :: MonadError TypeError m => ParamTerm k -> m (Inductive, [ParamTerm k])
> collectApps t = second reverse <$> collect t
>     where
>         collect (App l r) = second (r:) <$> collect l
>         collect (Ind i) = return (i, [])
>         collect _ = throwError NotInductive

Unlike the previous two "casts", we need to perform type inference to ensure
that a type constructor is fully applied and well formed. Thus, we forego the `intoInductive`
function, and jump straight into `inferI`.

> inferI :: MonadInfer k m => ParamTerm k -> m (Inductive, [ParamTerm k])
> inferI t = eval <$> infer t >>= \tt -> inferS tt >> collectApps tt

Next, we have to be careful about the rules of the Calculus of Constructions. We
can't _just_ put a type straight from a lambda into the environment; it so happens
that our types can be ill-formed! Thus, we need to first verify
the well-formedness of our argument type (for that, it must be well formed _and_ a sort). 
Furthermore, because types in the environment can refer to terms via DeBrujin
indices, we must be careful to preserve these references inside the body of a lambda
abstraction, leading us to use `offsetFree`. Thus, extending the environment looks like this:

> extend :: MonadInfer k m => ParamTerm k -> m a -> m a
> extend t m = extend' t $ const m
>
> extend' :: MonadInfer k m => ParamTerm k -> (Sort -> m a) -> m a
> extend' t f = do
>     s <- inferS t
>     b <- pop
>     local (map (second $ offsetFree 1) . ((b,t):)) (f s)
>
> extendAll :: MonadInfer k m => [ParamTerm k] -> m a -> m a
> extendAll = flip (foldr extend)

The Calculus of Constructions has cumulativity, and one of the rules for product
types requires both input types \\(A\\) and \\(B\\) to be of the same sort \\(\\text{Type}_i\\). This
need not be the case out of the box; however, types in CoC are
{{< sidenote "right" "semilattice-note" "a join semilattice," >}}
In our implementation they're actually a total order. However, in languages like Coq,
there are "two" base types, Prop and Set. Thus, in the "real world", we don't have
a total order, but we do have a join semilattice.
{{< /sidenote >}} and we can use our "join" function (aka "max") to find the supremum.

> joinS :: Sort -> Sort -> Sort
> joinS Prop Prop = Prop
> joinS (Type i) (Type j) = Type $ max i j
> joinS (Type i) _ = Type i
> joinS _ (Type i) = Type i

We should also write some code to perform type checking on entire modules.
For this, we need a way to verify the validity of a function. It is more
convenient to use the `extendAll` function from inside the monad,
since it will verify the validity of the environment.

> checkFunction :: MonadInfer Void m => Function -> m Term
> checkFunction f = do
>     ft <- eval <$> (extendAll (fArity f) $ infer $ fBody f)
>     let rt = eval (fType f)
>     guardE (TypeMismatch ft rt) $ ft == rt
>     return ft

Finally, we check an entire module by extracting all the function
definitions, and running `checkFunction` on each of them in turn.

> checkModule :: Module -> Either TypeError ()
> checkModule m = runInferE
>     $ mapM_ checkFunction $ catMaybes
>     $ map (asFunction . dContent) $ Map.elems $ mDefinitions m
