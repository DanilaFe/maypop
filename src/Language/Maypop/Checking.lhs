Let's work on type inference a little.

{{< todo >}}Seems like it would make sense to describe each case of Infer here.{{< /todo >}}

> {-# LANGUAGE FlexibleContexts #-}
> module Language.Maypop.Checking where
> import Language.Maypop.Syntax
> import Language.Maypop.Eval
> import Language.Maypop.Modules
> import Control.Monad.Reader
> import Control.Monad.Except
> import Data.Bifunctor
> import Data.Bool
> import Data.Void
> import Data.Maybe
> import qualified Data.Map as Map

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

It is also helpful to write a function that ensures a boolean condition
is met, failing if it isn't. Aside from the condition, we need to
provide information about what actually went wrong, in the form
of a `TypeError`:

> guardE :: MonadError te m => te -> Bool -> m ()
> guardE e = bool (throwError e) (return ())

Finally, on to the type inference function. We use the `MonadReader`
typeclass to require read-only access to the local environment \\(\\Gamma\\).

> infer :: (MonadReader [Term] m, MonadError TypeError m) => Term -> m Term
> infer (Ref n) = nth n <$> ask >>= maybe (throwError (FreeVariable n)) return
> infer (Fun f) = return $ fFullType f
> infer (Param p) = absurd p
> infer (Abs t b) = Prod t <$> extend t (infer b)
> infer (App f a) = do
>     (ta, tb) <- inferP f
>     targ <- infer a
>     if eval ta == eval targ
>      then return (substitute 0 a tb)
>      else throwError $ TypeMismatch (eval ta) (eval targ)
> infer (Let l i) = infer l >>= flip extend (infer i)
> infer (Prod a b) = extend' a $ \ua -> inferS b >>= \ub -> return $ Sort $
>     case ub of
>         Prop -> Prop
>         t -> joinS ua t
> infer (Sort u) = return $ Sort $ nextSort u
> infer (Constr i ci) = withConstr $
>     \c -> return $ foldr Prod (cReturn c) (iParams i ++ cParams c)
>     where
>         mConstr = nth ci $ iConstructors i
>         withConstr f = maybe (throwError UnknownConstructor) f mConstr
>         cParamRefs c = map (+length (cParams c)) [0..length (iParams i) -1]
>         cIndParams c = map Ref $ reverse $ cParamRefs c
>         cReturn c = foldl App (Ind i) $ cIndParams c ++ cIndices c
> infer (Ind i) = return $ foldr Prod (Sort $ iSort i) $ (iParams i ++ iArity i)
> infer (Case t i tt ts) = do
>     (i', is) <- inferI t
>     guardE TypeError $ i == i'
>     let (ps, inds) = splitAt (length $ iParams i) is
>     let subPs off = substituteMany off (map (offsetFree off) ps)
>     let tType = foldl App (Ind i) is
>     let constr (ci,c) b = do
>          let cps = zipWith subPs [0..] $ cParams c
>          let inds' = map (subPs $ length cps) $ cIndices c
>          let rcps = map (Ref . negate) $ [1..length cps]
>          let expt = foldl App (Constr i ci) $ rcps
>          let et = substituteMany 0 (expt:inds') tt
>          at <- substituteMany 0 rcps <$> (extendAll cps $ infer b)
>          guardE (TypeMismatch (eval at) (eval et)) $ eval at == eval et
>     let ar = zipWith (\n -> offsetFree 1 . subPs n) [0..] $ iArity i
>     extendAll (tType: ar) $ inferS tt
>     zipWithM constr (zip [0..] $ iConstructors i) ts
>     return $ substituteMany 0 (t:inds) tt
>
> runInfer :: Term -> Either TypeError Term
> runInfer = runInfer' []

> runInfer' :: [Term] -> Term -> Either TypeError Term
> runInfer' ts t = runReader (runExceptT $ infer t) ts

There are a few utility functions in the above definitions; let's take a look
at all of them in turn.  First up is `inferS`. We need this function because
not all terms consitute valid types. For instance, a lambda function is _not_ a
type, but it is a term. Indeed, computation aside, only the `Sort` constructor corresponds
to a valid type. However, some constructs in the Calculus of Constructions specifically require types,
such as \\(\\Pi\\). Thus, we'll define a way to "cast" a term into a valid sort. This will
be used to discard terms such as \\(\\Pi(\\lambda \\text{Prop}.0),\\text{Prop}\\), which have non-types in a
place where a type is needed.

> intoSort :: MonadError TypeError m => Term -> m Sort
> intoSort (Sort u) = return u
> intoSort _ = throwError NotSort

We can use this to define a specialized version of `infer`:

> inferS :: (MonadReader [Term] m, MonadError TypeError m) => Term -> m Sort
> inferS t = eval <$> infer t >>= intoSort

A similar casting function to `intoSort` is `intoProduct`, which helps
us require that a term is a dependent product (this is used for the application rule).
We return the two terms composing a product type rather than returning a `Term`, which
helps the type system "remember" that this is not just any term that passed our inspection.

> intoProduct :: MonadError TypeError m => Term -> m (Term, Term)
> intoProduct (Prod a b) = return (a, b)
> intoProduct _ = throwError NotProduct

Once again, we define a specailized version of `infer` for products:

> inferP :: (MonadReader [Term] m, MonadError TypeError m) => Term -> m (Term, Term)
> inferP t = eval <$> infer t >>= intoProduct

Just as we may want to cast a data type into a product, we may also want to cast
it into an inductive data type, extracting the parameters and indices. Things
are a little trickier here, since fully applied inductive type constructors
are represented as a chain of `App` nodes. We thus define a function to turn this
tree into a list:

> collectApps :: MonadError TypeError m => Term -> m (Inductive, [Term])
> collectApps t = second reverse <$> collect t
>     where
>         collect (App l r) = second (r:) <$> collect l
>         collect (Ind i) = return (i, [])
>         collect _ = throwError NotInductive

Unlike the previous two "casts", we need to perform type inference to ensure
that a type constructor is fully applied and well formed. Thus, we forego the `intoInductive`
function, and jump straight into `inferI`.

> inferI :: (MonadReader [Term] m, MonadError TypeError m) => Term -> m (Inductive, [Term])
> inferI t = eval <$> infer t >>= \tt -> inferS tt >> collectApps tt

Next, we have to be careful about the rules of the Calculus of Constructions. We
can't _just_ put a type straight from a lambda into the environment; it so happens
that our types can be ill-formed! Thus, we need to first verify
the well-formedness of our argument type (for that, it must be well formed _and_ a sort). 
Furthermore, because types in the environment can refer to terms via DeBrujin
indices, we must be careful to preserve these references inside the body of a lambda
abstraction, leading us to use `offsetFree`. Thus, extending the environment looks like this:

> extend :: (MonadReader [Term] m, MonadError TypeError m) => Term -> m a -> m a
> extend t m = extend' t $ const m
>
> extend' :: (MonadReader [Term] m, MonadError TypeError m) => Term -> (Sort -> m a) -> m a
> extend' t f = inferS t >>= \u -> local (map (offsetFree 1) . (t:)) (f u)
>
> extendAll :: (MonadReader [Term] m, MonadError TypeError m) => [Term] -> m a -> m a
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

> checkFunction :: (MonadReader [Term] m, MonadError TypeError m) => Function -> m Term
> checkFunction f = do
>     ft <- extendAll (fArity f) $ infer $ fBody f
>     guardE (TypeMismatch (eval ft) (eval (fType f))) $ eval ft == eval (fType f)
>     return ft
>
> checkModule :: Module -> Either TypeError ()
> checkModule m = runReader (runExceptT $ mapM_ checkFunction $ catMaybes $ map (asFunction . dContent) $ Map.elems $ mDefinitions m) []
