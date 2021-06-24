In this module we define unification contexts, which are essential for the correct operation
of our type inference.

> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE TypeFamilies #-}
> module Language.Maypop.Context where
> import Language.Maypop.Syntax
> import Language.Maypop.InfiniteList
> import Language.Maypop.Unification
> import Control.Applicative
> import Control.Monad
> import Control.Monad.Reader
> import Data.Maybe

Unification is imposible to do by simply recursively considering two terms by themselves.
This is particularly true in the DeBrujin case: a different index can represent the exact
same variable, and identical DeBrujin indices can reference differing binders. At the
very least, we need to bundle the "value" of a unification variable with the number
of surrounding binders; this would be used when comparing potentially different
DeBrujin indices. For example, the term `Ref 0` with no surrounding binders
should unify with a term `Ref 1` with one surrounding binder.

The number of surrounding binders is, in actuality, insufficient. Consider,
for example, the expression \\(\\text{pair}\\ (\\lambda. ?1)\\ (\\lambda. ?2)\\),
where our unification variables are written as \\(?1\\) and \\(?2\\). These
two variables, despite having the same number of surrounding binders, should not
be unifiable; the variables introduced by the two lambda abstactions are not
in any way related, so if we were eventually to discover that \\(?1\\) is
the DeBrujin index \\(0\\), this would not be the same as the DeBrujin
index \\(0\\) in the position of \\(?2\\). To enforce this, we have to
annotate each binder we come across with a unique identifier, perhaps as
\\(\\text{pair}\\ (\\lambda^a. ?1)\\ (\\lambda^b. ?2)\\). Then, DeBrujin
indices effectively become \\(0^a\\) and \\(0^b\\): clearly two different things.

{{< todo >}}Out of date.{{< /todo >}}
Finally, it is useful to know the type of a particular unification variable. We may
not always know it, but in such cases, we can always represent this type by yet
another unification variable. This is the last piece we need to define our `Context`
data type:

> data Context b k = Context
>     { ctxBinders :: [b]
>     , ctxType :: Maybe (ParamTerm k)
>     , ctxValue :: Maybe (ParamTerm k)
>     }
>     deriving Show

In the above, the actual value of a particular unification variable, `ctxValue`,
is held in a `Maybe`, since the context of a unification variable can be known
without knowing its association.

When unifying two contexts, we need to find the "least common denominator" of
the surrounding binders, and esnure that each of the two values can exist in both.
For example, when unifying \\([a,b] 1\\) (the DeBrujin index \\(1\\) surrounded
by binders identified \\(a\\) and \\(b\\)) with \\([b], 0\\), we note
that they can unify if the former context can be "narrowed" to only
include \\(b\\), and not \\(a\\) (indeed, doing so makes the two contexts identical).
In logic, removing an assumption from a judgement while maintaining its validity is called "strengthenning",
and this corresponds pretty much exactly to what we're doing here.
To strengthen an expression by removing \\(n\\) binders from the surrounding
context, we need to subtract \\(n\\) from each free variable in that expression
(you can see that when, while removing the single \\(a\\) from the context in
the previous example, we reduce the DeBrujin index from \\(1\\) to \\(0\\)).
This isn't always safe to do (much like it's not always safe to remove an
assumption from a judgement); in our case, the issue would occur if one of the
free variables being modified was made negagive. Thus, we define our
strengthenning function as returning a value wrapped in some `MonadPlus m`,
where `mzero` represents strengthenning failure. Conveniently,
we can use the `transform` function from the `Syntax` module to do this,
since it works in arbitrary monadic contexts, and since its entire purpose is
to manipulate free variables.

> strengthen :: MonadPlus m => Int -> ParamTerm k -> m (ParamTerm k)
> strengthen n t = runReaderT (transform op t) 0
>     where op k = ask >>= \x -> if k - x >= n then return $ Ref (k-n) else mzero

We can define a corresponding `weaken` function, which does he opposite. This function
doesn't fail (if a term is well-typed in some context, adding new variables does not
change this), and turns out to be equivalent to `offsetFree`:

> weaken :: Int -> ParamTerm k -> ParamTerm k
> weaken = offsetFree

All that's left now is to determine the "shared" part of the two sets of surrounding
binders. We do this with a function `common`:

> common :: Eq a => [a] -> [a] -> [a]
> common l1 l2 = common' (reverse l1) (reverse l2) []
>     where
>         common' (x:xs) (y:ys) acc | x == y = common' xs ys (x:acc)
>         common' _ _ acc = acc

Now, we can define a function that, given a common prefix computed with `common`,
attempts to strengthen a context's term. If the term is not known, then strengthenning
trivially succeeds, still resulting in a `Nothing` term.

> matchPrefix :: (Eq k, MonadPlus m) => [b] -> (Context b k -> (Maybe (ParamTerm k))) -> Context b k -> m (Maybe (ParamTerm k))
> matchPrefix bs f ctx = traverse (strengthen by) (f ctx)
>     where by = length (ctxBinders ctx) - length bs

One we have two such strengthened terms, both wrapped in `Maybe`s, we need to combine them.
The behavior we expect is _almost_ like that of `Maybe`'s `Semigroup` instance, in
which two `Nothing` values produce `Nothing`, one `Just` and one `Nothing` returns the
`Just`, and two `Just` values have their contents combined with `(<>)`. Unfortunately,
unifying two terms cannot be turned into a `(<>)` operation, since it requires an additional
argument in the form of the shared binders. Furthermore, unification's result is a monad,
whereas we still want to extract a `Maybe (ParamTerm k)`. We are thus forced to define a more general
operation `combine`:

> combine :: Monad m => (a -> a -> m a) -> Maybe a -> Maybe a -> m (Maybe a)
> combine f Nothing b = return b
> combine f a Nothing = return a
> combine f (Just a) (Just b) = Just <$> f a b

Finally, it's time to move on to something a bit harder. Supposing that we are unifying two
contexts, we need a way to unify the constituent terms. We cannot, however, rely on
a `Unifiable` instance for these terms; even though we're inspecting terms, we're still
collecting information about entire contexts. We thus define a standalone term unification
function as follows:

> unifyInContext
>     :: (Eq k, MonadUnify k (Context b k) m, MonadInf b m)
>     => [b] -> ParamTerm k -> ParamTerm k -> m (ParamTerm k)
> unifyInContext bs t1 t2 = runReaderT (unify' t1 t2) bs
>     where
>         unify' (Ref x1) (Ref x2) | x1 == x2 = return $ Ref x1
>         unify' (Fun f1) (Fun f2) | f1 == f2 = return $ Fun f1
>         unify' (Abs l1 r1) (Abs l2 r2) =
>             liftA2 Abs (unify' l1 l2) (withBinder $ unify' r1 r2)
>         unify' (App l1 r1) (App l2 r2) =
>             liftA2 App (unify' l1 l2) (unify' r1 r2)
>         unify' (Let l1 r1) (Let l2 r2) =
>             liftA2 Let (unify' l1 l2) (withBinder $ unify' r1 r2)
>         unify' (Prod l1 r1) (Prod l2 r2) =
>             liftA2 Prod (unify' l1 l2) (withBinder $ unify' r1 r2)
>         unify' (Sort s1) (Sort s2) | s1 == s2 = return $ Sort s1
>         unify' (Ind i1) (Ind i2) | i1 == i2 = return $ Ind i1
>         unify' (Constr i1 ci1) (Constr i2 ci2)
>             | i1 == i2 && ci1 == ci2 = return $ Constr i1 ci1
>         unify' (Case t1 i1 tt1 ts1) (Case t2 i2 tt2 ts2)
>             | i1 == i2 = Case
>                 <$> unify' t1 t2
>                 <*> pure i1
>                 <*> withRet i1 (unify' tt1 tt2)
>                 <*> withBranches i1 (zipWith unify' ts1 ts2)
>         unify' (Param k1) (Param k2) =
>             bindTerm k1 Nothing >> merge k1 k2 >> return (Param k1)
>         unify' (Param k1) t = bindTerm k1 (Just t) >> return t
>         unify' t (Param k2) = bindTerm k2 (Just t) >> return t

The above function works pretty much as wed expect. Every time we encounter a new
binder, we generate a unique name for it via `withBinder` (which itself calls
`pop` and retrieves a name from our infinite list of fresh names). We track
these various identifier in a stack (where the top of the stack corresponds
to the innermost binder), which we carry around using a `Reader` monad. Whenever
we encounter a unification variable, we use `bindTerm` to augment it with the
current binding context, which it must be compatible with.

> withRet :: (MonadReader [b] m, MonadInf b m) => Inductive -> m a -> m a
> withRet i = withBinders (1 + length (iArity i))
>
> withConstr :: (MonadReader [b] m, MonadInf b m) => Constructor -> m a -> m a
> withConstr c = withBinders (length (cParams c))
>
> withBranches :: (MonadReader [b] m, MonadInf b m) => Inductive -> [m a] -> m [a]
> withBranches i = sequence . zipWith withConstr (iConstructors i)
>
> withBinder :: (MonadReader [b] m, MonadInf b m) => m a -> m a
> withBinder m = pop >>= \x -> local (x:) m

> withBinders :: (MonadReader [b] m, MonadInf b m) => Int -> m a -> m a
> withBinders n m = popN n >>= \xs -> local (xs++) m

> bindTerm
>     :: (MonadReader [b] m, MonadInf b m, MonadUnify k (Context b k) m)
>     => k -> Maybe (ParamTerm k) -> m ()
> bindTerm k mt = do
>     bs' <- ask
>     void $ bind k (Context bs' Nothing mt)

Just as we need a standalone term unification function to perform context
unification, we also need a standalone term _substitution_ function to
perform context substitution. In this case, we begin substitution in
some context `bs`, attempting to substitute some parameter `k` in
a term `t` with the term from another context `ctx`. To help re-use
our existing logic, we once again take advantage of `MonadReader` and `MonadInf`;
however, we start the `MonadInf` anew, and thus, cannot rely on the uniqueness
of names. We merely use our new stack of names to count the number of surrounding
binders.

> substituteInContext :: (Eq k, Infinite b) => [b] -> k -> Context b k -> ParamTerm k -> ParamTerm k
> substituteInContext bs k ctx t = runInf (runReaderT (subst t) bs)
>     where
>         subst t@(Param k') | k == k' = do
>             bs' <- ask
>             let off = length (ctxBinders ctx) - length bs'
>             let st' = if off >= 0
>                  then ctxValue ctx >>= strengthen off
>                  else weaken (-off) <$> ctxValue ctx
>             return $ fromMaybe t st'
>         subst (Abs l r) = liftA2 Abs (subst l) (withBinder $ subst r)
>         subst (App l r) = liftA2 App (subst l) (subst r)
>         subst (Let l r) = liftA2 Let (subst l) (withBinder $ subst r)
>         subst (Prod l r) = liftA2 Prod (subst l) (withBinder $ subst r)
>         subst (Case t i tt ts) = Case
>             <$> subst t
>             <*> pure i
>             <*> withRet i (subst tt)
>             <*> withBranches i (map subst ts)
>         subst t = return t

Now that we know how to unify and substitute terms, we can finally
define `Unifiable` for `Context b k`.

> combineTerms
>     :: (Eq k, MonadUnify k (Context b k) m, MonadInf b m)
>     => [b] -> (Context b k -> Maybe (ParamTerm k))
>     -> Context b k -> Context b k -> m (Maybe (ParamTerm k))
> combineTerms bs f ct1 ct2 = join
>     $ combine (unifyInContext bs)
>     <$> (matchPrefix bs f ct1)
>     <*> (matchPrefix bs f ct2)

> instance (Eq k, Eq b, Infinite b) => Unifiable k (Context b k) where
>     type ExtraClass (Context b k) m = MonadInf b m
>
>     unify ct1 ct2 = do
>         let prefix = common (ctxBinders ct1) (ctxBinders ct2)
>         mt <- combineTerms prefix ctxType ct1 ct2
>         mv <- combineTerms prefix ctxValue ct1 ct2
>         return $ Context prefix mt mv
>     occurs k ctx = fromMaybe False
>         $ liftA2 (||) (elem k <$> ctxType ctx) (elem k <$> ctxValue ctx)
>     substitute k ct ct' = ct'
>         { ctxValue = substituteInContext (ctxBinders ct') k ct <$> ctxValue ct'
>         , ctxType = substituteInContext (ctxBinders ct') k ct <$> ctxType ct'
>         }
