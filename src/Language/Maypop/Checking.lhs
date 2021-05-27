Let's work on type inference a little.

{{< todo >}}Seems like it would make sense to describe each case of Infer here.{{< /todo >}}

> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE MonoLocalBinds #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> module Language.Maypop.Checking where
> import Language.Maypop.Syntax
> import Language.Maypop.Eval
> import Language.Maypop.Modules
> import Language.Maypop.InfiniteList
> import Language.Maypop.Unification hiding (substitute)
> import Control.Monad.Reader
> import Control.Monad.Except
> import Control.Monad.Writer
> import Control.Applicative
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

{{< todo >}} Explain this {{< /todo >}}

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

> class (Ord k, MonadReader (InferEnv k) m, MonadError TypeError m, MonadUnify k (ParamTerm k) m) => MonadInfer k m where
> instance (Ord k, MonadReader (InferEnv k) m, MonadError TypeError m, MonadUnify k (ParamTerm k) m) => MonadInfer k m where

{{< todo >}}Explain this {{< /todo >}}

> data InferEnv k = InferEnv
>     { ieRefs :: [ParamTerm k]
>     , ieParams :: Map.Map k (ParamTerm k)
>     }
>
> pushRef :: ParamTerm k -> InferEnv k -> InferEnv k
> pushRef t ie = ie { ieRefs = map (offsetFree 1) $ t : ieRefs ie }
>
> setParams :: Map.Map k (ParamTerm k) -> InferEnv k -> InferEnv k
> setParams ps ie = ie { ieParams = ps }

Finally, on to the type inference function. We use the `MonadReader`
typeclass to require read-only access to the local environment \\(\\Gamma\\).

> infer :: MonadInfer k m => ParamTerm k -> m (ParamTerm k)
> infer (Ref n) = (nth n . ieRefs) <$> ask >>= maybe (throwError (FreeVariable n)) return
> infer (Fun f) = return $ parameterize $ fFullType f
> infer (Fix f) = return $ parameterize $ fFullType $ fxFun f
> infer (Param p) = (Map.lookup p . ieParams) <$> ask >>= maybe (throwError TypeError) return
> infer (Abs t b) = Prod t <$> extend t (infer b)
> infer (App f a) = do
>     (ta, tb) <- inferP f
>     targ <- infer a
>     unify (eval ta) (eval targ)
>     reify $ substitute 0 a tb
> infer (Let l i) = infer l >>= flip extend (infer i)
> infer (Prod a b) = extend' a $ \ua -> inferS b >>= \ub -> return $ Sort $
>     case ub of
>         Prop -> Prop
>         t -> joinS ua t
> infer (Sort u) = return $ Sort $ nextSort u
> infer (Constr i ci) = withConstr $
>     \c -> return $ foldr Prod (parameterize $ cReturn c) (parameterizeAll $ map snd $ iParams i ++ cParams c)
>     where
>         mConstr = nth ci $ iConstructors i
>         withConstr f = maybe (throwError UnknownConstructor) f mConstr
>         cParamRefs c = map (+length (cParams c)) [0..length (iParams i) -1]
>         cIndParams c = map Ref $ reverse $ cParamRefs c
>         cReturn c = foldl App (Ind i) $ cIndParams c ++ cIndices c
> infer (Ind i) = return $ foldr Prod (Sort $ iSort i) $ (parameterizeAll $ map snd (iParams i) ++ iArity i)
> infer (Case t i tt ts) = do
>     (i', is) <- inferI t
>     guardE TypeError $ i == i'
>     let (ps, inds) = splitAt (length $ iParams i) is
>     let subPs off = substituteMany off (map (offsetFree off) ps)
>     let tType = foldl App (Ind i) is
>     let constr (ci,c) b = do
>          let cps = zipWith subPs [0..] $ parameterizeAll $ map snd $ cParams c
>          let inds' = map (subPs $ length cps) $ parameterizeAll $ cIndices c
>          let rcps = map (Ref . negate) $ [1..length cps]
>          let expt = foldl App (Constr i ci) $ rcps
>          let et = substituteMany 0 (expt:inds') tt
>          at <- substituteMany 0 rcps <$> (extendAll cps $ infer b)
>          unify (eval at) (eval et)
>     let ar = zipWith (\n -> offsetFree 1 . subPs n) [0..] $ parameterizeAll $ iArity i
>     extendAll (tType: ar) $ inferS tt
>     zipWithM constr (zip [0..] $ iConstructors i) ts
>     return $ substituteMany 0 (t:inds) tt
>
> type InferE a = UnifyEqT Term (ExceptT TypeError (Reader (InferEnv Void))) a
>
> runInferE :: [Term] -> InferE a -> Either TypeError a
> runInferE ts m = runReader (runExceptT $ runUnifyEqT m) (InferEnv ts Map.empty)
>
> type InferU k a = UnifyT k (ParamTerm k) (ExceptT TypeError (Reader (InferEnv k))) a
>
> runInferU :: (Ord k, Infinite k) => InferEnv k -> InferU k a -> Either TypeError a
> runInferU ie m = runReader (runExceptT $ runUnifyT m) ie
>
> runInfer :: Term -> Either TypeError Term
> runInfer = runInfer' []
>
> runInfer' :: [Term] -> Term -> Either TypeError Term
> runInfer' ts = runInferE ts . infer

There are a few utility functions in the above definitions; let's take a look
at all of them in turn.  First up is `inferS`. We need this function because
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
>         intoProduct t' <|> (freshProd >>= unify t' >>= intoProduct)
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
> extend' t f = inferS t >>= \u -> local (pushRef t) (f u)
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

> checkFunction :: MonadInfer Void m => Function -> m Term
> checkFunction f = do
>     ft <- extendAll (map snd $ fArity f) $ infer $ fBody f
>     guardE (TypeMismatch (eval ft) (eval (fType f))) $ eval ft == eval (fType f)
>     return ft
>
> checkModule :: Module -> Either TypeError ()
> checkModule m = runInferE [] $ mapM_ checkFunction $ catMaybes $ map (asFunction . dContent) $ Map.elems $ mDefinitions m

{{< todo >}} new stuff below {{< /todo >}}

> instantiate :: (MonadWriter [(k, ParamTerm k)] m,  MonadUnify k (ParamTerm k) m) => ParamTerm () -> m (ParamTerm k)
> instantiate = traverse (const inst)
>     where
>         inst = do
>             x <- fresh
>             xt <- fresh
>             tell [(x, Param xt)]
>             return $ x
>
> strip :: ParamTerm a -> Maybe Term
> strip (Ref i) = Just $ Ref i
> strip (Fun f) = Just $ Fun f
> strip (Fix f) = Just $ Fix f
> strip Param{} = Nothing
> strip (Abs l r) = liftA2 Abs (strip l) (strip r)
> strip (App l r) = liftA2 App (strip l) (strip r)
> strip (Let l r) = liftA2 Let (strip l) (strip r)
> strip (Prod l r) = liftA2 Prod (strip l) (strip r)
> strip (Sort s) = Just $ Sort s
> strip (Constr c ci) = Just $ Constr c ci
> strip (Ind i) = Just $ Ind i
> strip (Case t i tt ts) = liftA3 (flip Case i) (strip t) (strip tt) (mapM strip ts)
>
> elaborate :: ParamTerm () -> Maybe Term
> elaborate pt = either (const Nothing) Just $ runInferU (InferEnv [] Map.empty) (elab :: InferU String Term)
>     where
>         elab = do
>             (ipt, ps) <- runWriterT (instantiate pt)
>             local (setParams $ Map.fromList ps) $ infer ipt
>             ipt' <- reify ipt
>             maybe (throwError TypeError) return (strip ipt')
