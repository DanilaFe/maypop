Here, we'll develop a general unification monad typeclas and transformer that will be
used for type inference.

> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE FunctionalDependencies #-}
> {-# LANGUAGE GeneralizedNewtypeDeriving #-}
> module Language.Maypop.Unification where
> import Language.Maypop.InfiniteList
> import Control.Monad.State
> import Control.Monad.Except
> import Control.Applicative
> import qualified Data.Map as Map
> import qualified Data.Set as Set
> import Data.Maybe

First of all, variables in our unification framework should have an infinite
supply. Instantiating a fresh variable is very common in unification; if would be
a shame if we ran out of variables, and started re-using! For this purpose,
we define a typeclass, `UnificationKey`, for types that can provide an infinite,
non-repeating list of their elements.

> class UnificationKey k where
>     keys :: InfList k

Next, we'll define an MTL-style typeclass that encapsulates unification functionality.
Since
{{< sidenote "right" "fail-note" "the unification operation can fail," >}}
For instance, what's the result of unifying the expressions <code>3</code> and <code>4</code>? 
{{< /sidenote >}}
we'll add a `MonadFail` constraint to the carrier monad. Other than that, our `MonadUnify`
typeclass will be parameterized by the type of the unification variables `k` and
type of the stuff bound to the unification variables `v`. We also require the
unification variables to be infinite (via `UnificationKey`), and for the values
being unified to be `Unifiable`.

> class (MonadError () m, Unifiable k v, UnificationKey k)
>         => MonadUnify k v m | m -> k, m -> v where
>     fresh :: m k
>     bind :: k -> v -> m v
>     merge :: k -> k -> m ()

What is `Unifiable`? It's simple enough; a type is unifiable if, given two values
of that type, you can perform unification, possibly yielding a single value of that
type (or, perhaps, failing).

> class Unifiable k v | v -> k where
>     unify :: MonadUnify k v m => v -> v -> m v

Let's define a monad transformer of this type, `UnifyT`. This will be a simple
wrapper around the `StateT` and `ExceptT` monads; however, __it will not
implement `MonadState` or `MonadError`__, since we want to keep unification state separate
from any other state the API user would want to create. We can use `deriving` to
automatically compute the `Functor`, `Applicative`, and `Monad` instances,
so the bulk of our work will be implementing the `MonadUnify` methods.

> newtype UnifyT k v m a
>     = MkUnifyT { unwrapUnifyT :: ExceptT () (StateT (UnificationState k v) m) a }
>     deriving (Functor, Applicative, Monad, MonadError ())

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
>     let bound' = foldr (flip Map.insert (ks, mv)) bound $ Set.toList ks
>     modify $ \s -> s { sBound = bound' }

Finally, we'll define a `MonadUnify` instance for `UnifyT`. In order
to make map lookups possible in `UnificationState`, we place an additional
`Ord` constraint on `k`. Since `UnifyT` is a monad transformer, this instance
is polymorphic over a generic monad `m`.

> instance (Unifiable k v, UnificationKey k, Ord k, Monad m) => MonadUnify k v (UnifyT k v m) where
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
> popVar :: UnificationState k v -> (k, UnificationState k v)
> popVar s = let Cons k ks = sVars s in (k, s { sVars = ks })
