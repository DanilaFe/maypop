Here, we'll develop a general unification monad typeclas and transformer that will be
used for type inference.

> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE FunctionalDependencies #-}
> {-# LANGUAGE GeneralizedNewtypeDeriving #-}
> {-# LANGUAGE TupleSections #-}
> {-# LANGUAGE UndecidableInstances #-}
> module Language.Maypop.Unification where
> import Language.Maypop.InfiniteList
> import Language.Maypop.Eval
> import Language.Maypop.Syntax hiding (occurs, substitute)
> import Control.Monad.State
> import Control.Monad.Reader
> import Control.Monad.Writer
> import Control.Monad.Logic
> import Control.Monad.Except
> import Control.Applicative
> import qualified Data.Map as Map
> import qualified Data.Set as Set
> import Data.Maybe
> import Data.Bifunctor
> import Data.Void
> import Data.Foldable

We'll define an MTL-style typeclass that encapsulates unification functionality.
Since
{{< sidenote "right" "fail-note" "the unification operation can fail," >}}
For instance, what's the result of unifying the expressions <code>3</code> and <code>4</code>? 
{{< /sidenote >}}
we'll add a `MonadFail` constraint to the carrier monad. Other than that, our `MonadUnify`
typeclass will be parameterized by the type of the unification variables `k` and
type of the stuff bound to the unification variables `v`. We also require the
unification variables to be infinite (via the `Infinite` typeclass from `InfiniteList`), and for the values
being unified to be `Unifiable`.

> class (Unifiable k v, MonadPlus m) => MonadUnify k v m | m -> k, m -> v where
>     fresh :: m k
>     bind :: k -> v -> m v
>     merge :: k -> k -> m ()
>     reify :: v -> m v
>     bound :: k -> m (Maybe v)

What is `Unifiable`? It's simple enough; a type is unifiable if, given two values
of that type, you can perform unification, possibly yielding a single value of that
type (or, perhaps, failing). We make this a multiparameter type class to encode
the fact that unification can produce bindings of variables (keys `k`).

While performing unification, we need to be careful: we don't want to yield
infinite terms! For instance, unifying `a ~ (b -> a)` can create the infinite
term `b -> b -> ...`. To avoid this, it's common to perform an "occurss check":
we see if the value being bound to a unification variable contains that
unification variable, and reject the binding in that case. The `Unifiable`
class needs to also provide such an `occurs` method.

Finally, when we're done performing unification, it would be very
nice to replace occurences of _bound_ variables with the values they
are bound to. For this, we also define a `substitute` method.

> class Unifiable k v | v -> k where
>     unify :: MonadUnify k v m => v -> v -> m v
>     occurs :: k -> v -> Bool
>     substitute :: MonadUnify k v m => k -> v -> v -> m v

With the three basic `Unifiable` operations in place, we can define
some helper functions. As we said before, unification should fail
when the "occurs check" fails; why not define a convenient little
operation to fail (in some monadic context `m` supporting exceptions)
when we detect an infinite type?

> guardOccurs :: (MonadPlus m, Unifiable k v) => k -> v -> m ()
> guardOccurs k v = if occurs k v then mzero else return ()

After we're done with unification, we can have an entire map of
variables and their bindings. We can define a little function that uses
the basic `substitute` method to apply an entire map (in the form of a list
of pairs) of unification bindings to our final value.

> substituteAll :: (MonadUnify k v m, Unifiable k v) => [(k, v)] -> v -> m v
> substituteAll m v = foldrM (uncurry substitute) v m

Next, let's define a monad transformer satisfying `MonadUnify`, which we'll call `UnifyT`. This will be a simple
wrapper around the `StateT` monad; however, __it will not
forward the `MonadState`__ API, since we want to keep unification state separate
from any other state the API user would want to create. We can use `deriving` to
automatically compute the `Functor`, `Applicative`, `Monad` and other instances,
so the bulk of our work will be implementing the `MonadUnify` methods.

> newtype UnifyT k v m a
>     = MkUnifyT { unwrapUnifyT :: StateT (UnificationState k v) m a }
>     deriving (Functor, Applicative, Monad, Alternative, MonadTrans, MonadPlus, MonadReader r, MonadWriter w, MonadError e)

For some reason, Haskell's `GeneralizedNewtypeDeriving` fails to compute the `MonadLogic`
instance for `UnifyT`. We write it manually, instead.

> instance (MonadPlus m, MonadLogic m) => MonadLogic (UnifyT k v m) where
>     msplit m = MkUnifyT $ fmap (second MkUnifyT <$>) $ msplit (unwrapUnifyT m)

Even though we don't expose the `MonadState` class from the underlying `StateT` monad
in `UnifyT`, we do allow the underlying monad `m` to have `MonadState`. Haskell will
not derive this instance (because `UnifyT` wraps a `StateT`), but it's straightforward
to manually define.

> instance MonadState s m => MonadState s (UnifyT k v m) where
>     get = lift $ get
>     put x = lift $ put x

Sometimes we want to spin up and throw away a `Writer` monad inside of `UnifyT`.
For this, we need `WriterT` to propagate `MonadUnify`:

> instance (Monoid w, MonadUnify k v m) => MonadUnify k v (WriterT w m) where
>     fresh = lift $ fresh
>     bind k v = lift $ bind k v
>     merge k1 k2 = lift $ merge k1 k2
>     reify v = lift $ reify v
>     bound k = lift $ bound k
>
> instance MonadUnify k v m => MonadUnify k v (StateT s m) where
>     fresh = lift $ fresh
>     bind k v = lift $ bind k v
>     merge k1 k2 = lift $ merge k1 k2
>     reify v = lift $ reify v
>     bound k = lift $ bound k
>
> instance MonadUnify k v m => MonadUnify k v (ReaderT r m) where
>     fresh = lift $ fresh
>     bind k v = lift $ bind k v
>     merge k1 k2 = lift $ merge k1 k2
>     reify v = lift $ reify v
>     bound k = lift $ bound k

Finally, we write a couple of functions to actually run computations inside
`UnifyT`:

> runUnifyT :: (Monad m, Infinite k, Unifiable k v) => UnifyT k v m a -> m a
> runUnifyT u = fst <$> runStateT (unwrapUnifyT u) emptyState
>
> runUnify :: (Infinite k, Unifiable k v) => UnifyT k v Maybe a -> Maybe a
> runUnify u = fst <$> runStateT (unwrapUnifyT u) emptyState

There are some helper functions we can define for our `UnifyT` type. For instance,
we want to retrieve data from the underlying `State` monad: we'd like to know which
of the keys are associated, and what values they're bound to. In case no keys are associated
and no value is bound, we want to return the dummy value of `({k}, Nothing)`, which
indicates that the key being looked up is only associated with itself, and is not
bound to anything. This is implemented by `lookupK`:

> lookupK :: (Ord k, Monad m) => k -> UnifyT k v m (Set.Set k, Maybe v)
> lookupK k = MkUnifyT $ fromMaybe (Set.singleton k, Nothing) <$> (gets $ Map.lookup k . sBound)

When we try to associate two keys, we want to make sure that _all_ keys in the map that
are known to be equal point to the same value. We thus iterate through all keys
associated with either of the keys being unified, and update the value they're
bound to. This is done by `syncKeys`:

> syncKeys :: (Ord k, Monad m) => Set.Set k -> Maybe v -> UnifyT k v m ()
> syncKeys ks mv = MkUnifyT $ do
>     bound <- gets sBound
>     let lks = Set.toList ks
>     let bound' = foldr (flip Map.insert (ks, mv)) bound $ lks
>     modify $ \s -> s { sBound = bound' }

When we bind a value to a key, we want to make sure that the
key referring to this value no longer occurs anywhere in
our substitution map. This is to ensure that occurs checks work
correctly: for a map \\(\\{k_1\\mapsto k_2\\}\\), the term
\\(k_1\\) does not syntactically contain \\(k_2\\), but binding
\\(k_2 \\mapsto k_1\\) is certainly not allowed. Thus, when
we introduce a binding \\(k_1 \\mapsto k_2\\), we will
take care to rewrite terms like \\(k_1\\) into \\(k_2\\).

> substituteInternal :: (Ord k, Infinite k, MonadPlus m, Unifiable k v) => Set.Set k -> v -> UnifyT k v m ()
> substituteInternal ks v = do
>     bound <- MkUnifyT $ gets sBound
>     let lks = Set.toList ks
>     let entry k m
>          | Just (ks', Just v') <- Map.lookup k m = do
>              sv <- substitute k v v'
>              return $ Map.insert k (ks', Just sv) m
>          | otherwise = return m
>     bound' <- foldrM entry bound lks
>     MkUnifyT $ modify $ \s -> s { sBound = bound' }

Finally, we'll define a `MonadUnify` instance for `UnifyT`. In order
to make map lookups possible in `UnificationState`, we place an additional
`Ord` constraint on `k`. Since `UnifyT` is a monad transformer, this instance
is polymorphic over a generic monad `m`.

> instance (Unifiable k v, Infinite k, Ord k, Monad m, MonadPlus m) => MonadUnify k v (UnifyT k v m) where
>     fresh = MkUnifyT $ do
>         (k, us) <- gets popVar
>         put us >> return k
>     bind k v = do
>         (ks, mv) <- lookupK k
>         v' <- reify v
>         mapM (`guardOccurs` v') $ Set.toList ks
>         v'' <- maybe (return v') (unify v') mv
>         syncKeys ks (Just v'')
>         substituteInternal ks v''
>         return v''
>     merge k1 k2 = do
>         (ks1, mv1) <- lookupK k1         
>         (ks2, mv2) <- lookupK k2
>         let ks = Set.union ks1 ks2
>         case (mv1, mv2) of
>             (Just v1, Just v2) -> do
>                 v <- unify v1 v2
>                 syncKeys ks (Just v)
>                 substituteInternal ks v
>             _ -> syncKeys ks $ mv1 <|> mv2
>     reify v = (MkUnifyT $ gets bindingList) >>= (`substituteAll` v) 
>     bound k = MkUnifyT $ gets ((>>= snd) . Map.lookup k . sBound)

Last but not least, we define a data type for the unification state.
This consists of two things:

* The bindings that we've already created in the process of unification,
stored in `sBound`.
* They keys (unification variables) that are as yet unbound, stored in `sVars`.

> data UnificationState k v = MkUnificationState { sBound :: Map.Map k (Set.Set k, Maybe v), sVars :: InfList k }

There are a few things we can implement for this data type. First of all,
it's nice to have a handle on a "blank canvas" unification state, in
which nothing has yet occured. This state has no variable bindings
(and thus, its map is `empty`), and the entire infinite list of keys
(ensured to be infinite by the `Infinite` typeclass) is just the branch new
version, `infList`.

> emptyState :: Infinite k => UnificationState k v
> emptyState = MkUnificationState Map.empty infList

Occasionally, we may want to replace all variables (whose values we know)
for the terms they map to. For this, we need to retrieve
the list of all variable bindings, which we will do using `bindingList`.

> bindingList :: UnificationState k v -> [(k, v)]
> bindingList = mapMaybe (\(k, (_, mv)) -> (k,) <$> mv) . Map.toList . sBound

Finally, we write down a helper function to retrive a fresh variable
name from a `UnificationState` (also returning the modified
version of the state in which the newly popped variable is
no longer in the "fresh" list):

> popVar :: UnificationState k v -> (k, UnificationState k v)
> popVar s = let Cons k ks = sVars s in (k, s { sVars = ks })

So now we have unification with variables. But there's a little discovery
to be made here: we can actually define a unification monad for things
that cannot contain variables at all. We represent this absence of keys
by using `Void` for the type of unification variables. It's pointless
to keep any kind of state when performing this kind of unification, since
no new bindings can ever be introduced; it is thus possible to represent
a "trivial unification" monad transformer as follows:

> newtype UnifyEqT v m a = MkUnifyEqT { runUnifyEqT :: m a }
>     deriving (Functor, Applicative, Monad, MonadReader r, MonadWriter w, MonadState s, MonadError e, Alternative, MonadPlus)

We can define a very boring instance of `MonadUnify` for this data type:

> instance (Unifiable Void v, MonadPlus m) => MonadUnify Void v (UnifyEqT v m) where
>     fresh = mzero
>     bind k _ = absurd k
>     merge k1 _ = absurd k1
>     reify v = return v
>     bound k = return (absurd k)

We now implement unification for our `Term` type. Two terms only unify if they are built
using the same constructor; thus, we mostly include those cases in our pattern matching.
For cases like `App`, `Abs`, and `Prod`, two recursive calls to `unify` suffice; however,
for more complex terms such as `Case`, we have to do testing to ensure that the non-`Term`
data matches, too.

> data ContextTerm k = Valid (ParamTerm k) | Invalid deriving Show
>
> data Context k = Context
>     { ctxEnv :: [ContextTerm k]
>     , ctxTerm :: Maybe (ParamTerm k)
>     } deriving Show
>
> shorten :: Int -> [ContextTerm k] -> [ContextTerm k]
> shorten i = map (offset (-i)) . drop i
>
> matchLength :: [ContextTerm k] -> [ContextTerm k] -> ([ContextTerm k], [ContextTerm k])
> matchLength ts1 ts2
>     | length ts1 > length ts2 = (shorten (length ts1 - length ts2) ts1, ts2)
>     | length ts1 < length ts2 = (ts1, shorten (length ts2 - length ts1) ts2)
>     | otherwise = (ts1, ts2)
>
> commonPrefix :: (Eq k, MonadUnify k (Context k) m) => [ContextTerm k] -> [ContextTerm k] -> m [ContextTerm k]
> commonPrefix l1 l2 = let (l1', l2') = matchLength l1 l2 in compare (reverse l1') (reverse l2') []
>     where
>         compare (Invalid:xs) (Invalid:ys) acc = compare xs ys (Invalid:acc)
>         compare ((Valid t1):xs) ((Valid t2):ys) acc =
>             unifyTerm acc t1 t2 >>= compare xs ys . (:acc) . Valid
>         compare _ _ acc = return acc
>
> strengthen :: (Show k, MonadPlus m) => Int -> ParamTerm k -> m (ParamTerm k)
> strengthen n t = runReaderT (transform op t) 0
>     where op k = ask >>= \x -> if k - x >= n then return $ Ref (k-n) else mzero

> weaken :: Int -> ParamTerm k -> ParamTerm k
> weaken = offsetFree
>
> matchContext :: (Show k, Eq k, MonadUnify k (Context k) m) => [ContextTerm k] -> Context k -> m (Maybe (ParamTerm k))
> matchContext pr c
>     | Just t <- ctxTerm c = Just <$> (strengthen (length (ctxEnv c) - length pr) t)
>     | otherwise = return Nothing
>
> combine :: Monad m => (a -> a -> m a) -> Maybe a -> Maybe a -> m (Maybe a)
> combine f (Just a) (Just b) = Just <$> f a b
> combine _ m@(Just a) _ = return m
> combine _ _ m@(Just a) = return m
> combine _ _ _ = return Nothing
>
> instance (Show k, Eq k) => Unifiable k (Context k) where
>     unify c1 c2 = do
>         prefix <- commonPrefix (ctxEnv c1) (ctxEnv c2)
>         t1 <- matchContext prefix c1
>         t2 <- matchContext prefix c2
>         t <- combine (unifyTerm prefix) t1 t2
>         return $ Context prefix t
>     occurs k ctx = any occ (ctxEnv ctx) || maybe False (occurs k) (ctxTerm ctx)
>         where
>             occ Invalid = False
>             occ (Valid t) = occurs k t
>     substitute k c1 c2 =
>         do
>             env' <- walk (reverse $ ctxEnv c2) []
>             term' <- traverse (substituteTerm k env' c1) (ctxTerm c2)
>             return $ Context env' term'
>         where
>             subst _ Invalid = return Invalid
>             subst acc (Valid t) = Valid <$> substituteTerm k acc c1 t
>             walk (x:xs) acc = return x >>= walk xs . (:acc)
>             walk _ acc = return acc
>
> offset :: Int -> ContextTerm k -> ContextTerm k
> offset i (Valid t) = Valid $ offsetFree i t
> offset _ Invalid = Invalid
>
> valid :: MonadReader [ContextTerm k] m => ParamTerm k -> m a -> m a
> valid t = local (map (offset 1) . (Valid t:))
>
> invalid :: MonadReader [ContextTerm k] m => m a -> m a
> invalid = local (map (offset 1) . (Invalid:))
>
> invalidN :: MonadReader [ContextTerm k] m => Int -> m a -> m a
> invalidN n m = foldr ($) m $ replicate n invalid
>
> constr :: MonadReader [ContextTerm k] m => Constructor -> m a -> m a
> constr c = invalidN (length (cParams c))
>
> branches :: MonadReader [ContextTerm k] m => Inductive -> [m a] -> m [a]
> branches i = sequence . zipWith constr (iConstructors i)
>
> return_ :: MonadReader [ContextTerm k] m => Inductive -> m a -> m a
> return_ i = invalidN (1 + length (iArity i))
>
> substituteTerm :: (Eq k, Show k, MonadUnify k (Context k) m) => k -> [ContextTerm k] -> Context k -> ParamTerm k -> m (ParamTerm k)
> substituteTerm k env ctx t = runReaderT (subst' t) env
>     where
>         subst' t'@(Param k') | k == k' = do
>             env' <- ask
>             let diff = length (ctxEnv ctx) - length env'
>             ct <- if diff >= 0
>                 then traverse (strengthen diff) (ctxTerm ctx)
>                 else return $ (weaken (-diff)) <$> (ctxTerm ctx)
>             prefix <- commonPrefix env' (ctxEnv ctx)
>             matchContext prefix ctx
>             return $ fromMaybe t' ct
>         subst' (Abs l r) = do
>             l' <- subst' l
>             Abs l' <$> (valid l' $ subst' r)
>         subst' (App l r) = liftA2 App (subst' l) (subst' r)
>         subst' (Let l r) = liftA2 Let (subst' l) (subst' r)
>         subst' (Prod l r) = do
>             l' <- subst' l
>             Prod l' <$> (valid l' $ subst' r)
>         subst' (Case t i tt ts) = do
>             t' <- subst' t
>             tt' <- return_ i $ subst' tt
>             ts' <- branches i $ map subst' ts
>             return $ Case t' i tt' ts'
>         subst' t = return t
>
> unifyTerm :: (Eq k, MonadUnify k (Context k) m) => [ContextTerm k] -> ParamTerm k -> ParamTerm k -> m (ParamTerm k)
> unifyTerm ctx t1 t2 = runReaderT (unify' t1 t2) ctx
>     where
>         unify' (Ref x1) (Ref x2) | x1 == x2 = return $ Ref x1
>         unify' (Fun f1) (Fun f2) | f1 == f2 = return $ Fun f1
>         unify' (Abs l1 r1) (Abs l2 r2) = do
>             l <- unify' l1 l2
>             r <- valid l $ unify' r1 r2
>             return $ Abs l r
>         unify' (App l1 r1) (App l2 r2) = liftA2 App (unify' l1 l2) (unify' r1 r2)
>         unify' (Let l1 r1) (Let l2 r2) = liftA2 Let (unify' l1 l2) (invalid $ unify' r1 r2)
>         unify' (Prod l1 r1) (Prod l2 r2) = do
>             l <- unify' l1 l2
>             r <- valid l $ unify' r1 r2
>             return $ Prod l r
>         unify' (Sort s1) (Sort s2) | s1 == s2 = return $ Sort s1
>         unify' (Constr ind1 ci1) (Constr ind2 ci2)
>             | ci1 == ci2 && ind1 == ind2 = return $ Constr ind1 ci1
>         unify' (Ind i1) (Ind i2) | i1 == i2 = return $ Ind i1
>         unify' (Case t1 ind1 tt1 ts1) (Case t2 ind2 tt2 ts2)
>             | ind1 == ind2 = do
>                 t <- unify' t1 t2
>                 tt <- return_ ind1 $ unify' tt1 tt2
>                 ts <- branches ind1 $ zipWith unify' ts1 ts2
>                 return $ Case t ind1 tt ts
>         unify' (Param k1) (Param k2) = do
>             env <- ask
>             bind k1 (Context env Nothing) >> merge k1 k2 >> return (Param k1)
>         unify' (Param k1) t = ask >>= bind k1 . (`Context` (Just t)) >> return t
>         unify' t (Param k2) = ask >>= bind k2 . (`Context` (Just t)) >> return t
>         unify' _ _ = mzero
>
> instance Eq k => Unifiable k (ParamTerm k) where
>     unify t1 t2 = unify' (eval t1) (eval t2)
>         where
>             unify' (Ref x1) (Ref x2) | x1 == x2 = return $ Ref x1
>             unify' (Fun f1) (Fun f2) | f1 == f2 = return $ Fun f1
>             unify' (Abs l1 r1) (Abs l2 r2) = liftA2 Abs (unify l1 l2) (unify r1 r2)
>             unify' (App l1 r1) (App l2 r2) = liftA2 App (unify l1 l2) (unify r1 r2)
>             unify' (Let l1 r1) (Let l2 r2) = liftA2 Let (unify l1 l2) (unify r1 r2)
>             unify' (Prod l1 r1) (Prod l2 r2) = liftA2 Prod (unify l1 l2) (unify r1 r2)
>             unify' (Sort s1) (Sort s2) | s1 == s2 = return $ Sort s1
>             unify' (Constr ind1 ci1) (Constr ind2 ci2)
>                 | ci1 == ci2 && ind1 == ind2 = return $ Constr ind1 ci1
>             unify' (Ind i1) (Ind i2) | i1 == i2 = return $ Ind i1
>             unify' (Case t1 ind1 tt1 ts1) (Case t2 ind2 tt2 ts2)
>                 | ind1 == ind2 = liftA3 (`Case` ind1) (unify t1 t2) (unify tt1 tt2) (zipWithM unify ts1 ts2)
>             unify' (Param k1) (Param k2) = merge k1 k2 >> return (Param k1)
>             unify' (Param k1) t = bind k1 t
>             unify' t (Param k2) = bind k2 t
>             unify' _ _ = mzero
>     occurs = elem
>     substitute k v = return . subst
>         where
>             subst (Abs l r) = Abs (subst l) (subst r)
>             subst (App l r) = App (subst l) (subst r)
>             subst (Prod l r) = Prod (subst l) (subst r)
>             subst (Case t i tt ts) = Case (subst t) i (subst tt) (map subst ts)
>             subst (Param k') | k == k' = v
>             subst t = t
