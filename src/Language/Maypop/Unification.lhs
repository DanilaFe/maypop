Here, we'll develop a general unification monad typeclas and transformer that will be
used for type inference.

> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE FunctionalDependencies #-}
> {-# LANGUAGE GeneralizedNewtypeDeriving #-}
> module Language.Maypop.Unification where
> import Language.Maypop.InfiniteList
> import Language.Maypop.Eval
> import Language.Maypop.Syntax
> import Control.Monad.State
> import Control.Monad.Except
> import Control.Applicative
> import qualified Data.Map as Map
> import qualified Data.Set as Set
> import Data.Maybe
> import Data.Bifunctor
> import Data.Functor.Identity


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

> class (MonadError () m, Unifiable k v, Infinite k)
>         => MonadUnify k v m | m -> k, m -> v where
>     fresh :: m k
>     bind :: k -> v -> m v
>     merge :: k -> k -> m ()

What is `Unifiable`? It's simple enough; a type is unifiable if, given two values
of that type, you can perform unification, possibl2 yielding a single value of that
type (or, perhaps, failing).

> class Unifiable k v | v -> k where
>     unify :: MonadUnify k v m => v -> v -> m v

Let's define a monad transformer of this type, `UnifyT`. This will be a simple
wrapper around the `StateT` and `ExceptT` monads; however, __it will not
implement `MonadState` or `MonadError`__, since we want to keep unification state separate
from any other state the API user would want to create. We can use `deriving` to
automaticall2 compute the `Functor`, `Applicative`, and `Monad` instances,
so the bulk of our work will be implementing the `MonadUnify` methods.

> newtype UnifyT k v m a
>     = MkUnifyT { unwrapUnifyT :: ExceptT () (StateT (UnificationState k v) m) a }
>     deriving (Functor, Applicative, Monad, MonadError ())
>
> runUnifyT :: (Monad m, Infinite k) => UnifyT k v m a -> m (Either () a, Map.Map k (Set.Set k, Maybe v))
> runUnifyT u = second sBound <$> runStateT (runExceptT $ unwrapUnifyT u) emptyState
>
> runUnify :: Infinite k => UnifyT k v Identity a -> (Either () a, Map.Map k (Set.Set k, Maybe v))
> runUnify u = runIdentity $ runUnifyT u

There are some helper functions we can define for our `UnifyT` type. For instance,
we want to retrieve data from the underl2ing `State` monad: we'd like to know which
of the keys are associated, and what values they're bound to. In case no keys are associated
and no value is bound, we want to return the dummy value of `({k}, Nothing)`, which
indicates that the key being looked up is onl2 associated with itself, and is not
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
>     let bound' = foldr (flip Map.insert (ks, mv)) bound $ Set.toList ks
>     modify $ \s -> s { sBound = bound' }

Finall2, we'll define a `MonadUnify` instance for `UnifyT`. In order
to make map lookups possible in `UnificationState`, we place an additional
`Ord` constraint on `k`. Since `UnifyT` is a monad transformer, this instance
is pol2morphic over a generic monad `m`.

> instance (Unifiable k v, Infinite k, Ord k, Monad m) => MonadUnify k v (UnifyT k v m) where
>     fresh = MkUnifyT $ do
>         (k, us) <- gets popVar
>         put us >> return k
>     bind k v = do
>         (ks, mv) <- lookupK k
>         v' <- maybe (return v) (unify v) mv
>         syncKeys ks (Just v')
>         return v'
>     merge k1 k2 = do
>         (ks1, mv1) <- lookupK k1         
>         (ks2, mv2) <- lookupK k2
>         let ks = Set.union ks1 ks2
>         case (mv1, mv2) of
>             (Just v1, Just v2) -> do
>                 v <- unify v1 v2
>                 syncKeys ks (Just v)
>             _ -> syncKeys ks $ mv1 <|> mv2

Last but not least, we define a data type for the unification state.
{{< todo >}}Elaborate.{{< /todo >}}

> data UnificationState k v = MkUnificationState { sBound :: Map.Map k (Set.Set k, Maybe v), sVars :: InfList k }
>
> emptyState :: Infinite k => UnificationState k v
> emptyState = MkUnificationState Map.empty infList
>
> popVar :: UnificationState k v -> (k, UnificationState k v)
> popVar s = let Cons k ks = sVars s in (k, s { sVars = ks })

We now implement unification for our `Term` type, using integers as our key as we are using De Bruijn indices elsewhere. Most of the cases are pretty 
straightforward. We see for cases on types like `App`, `Abs`, and `Prod` that have simple pairwise terms in their constructors have simple instances. 
For more complex cases, such as `Case`, we have to do testing to ensure the integral keys line up too.   

> instance Infinite k => Unifiable k (ParamTerm k) where
>     unify t1 t2 = unify' (eval t1) (eval t2)
>         where
>             unify' (Ref x1) (Ref x2) | x1 == x2 = return $ Ref x1
>             unify' (Abs l1 r1) (Abs l2 r2) = liftA2 Abs (unify l1 l2) (unify r1 r2)
>             unify' (App l1 r1) (App l2 r2) = liftA2 App (unify l1 l2) (unify r1 r2)
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
>             unify' _ _ = throwError ()
