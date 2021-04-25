> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE AllowAmbiguousTypes #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE FunctionalDependencies #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE GeneralizedNewtypeDeriving #-}
> module Language.Maypop.Unification where
> import Language.Maypop.InfiniteList
> import Control.Monad.State
> import Control.Applicative
> import Data.Maybe
> import qualified Data.Map as Map
>
> type Key = String
>
> class Unifiable v where
>     unify :: MonadUnify v m => v -> v -> m ()
>
> class Monad m => MonadUnify v m | m -> v where
>     newVar    :: m Key
>     bindVar   :: Key -> v -> m ()
>     unifyVar  :: Key -> Key -> m ()
>
> data UnificationState v = MkUState { vars :: Map.Map Key v, names :: InfList Key }
>
> newtype UnifyT v m a = MkUnifyT { unUnifyT :: StateT (UnificationState v) m a } deriving (Functor, Applicative, Monad)
>
> instance (Monad m, Unifiable v) => MonadUnify v (UnifyT v m) where
>     newVar = MkUnifyT $ do
>         Cons k ks <- gets names
>         modify $ \s -> s { names = ks }
>         return k
>     bindVar k v = MkUnifyT $ modify $ \s -> s { vars = Map.insert k v (vars s) }
>     unifyVar k1 k2 = do
>             (v1, v2) <- fromJust <$> findKeys
>             unify v1 v2
>         where
>             findKeys = MkUnifyT $ liftA2 (liftA2 (,)) (findKey k1) (findKey k2)
>             findKey k = gets $ Map.lookup k . vars
>
> data DumTerm = Var Key | Lit Int
>
> instance Unifiable DumTerm where
>     unify (Var k1) (Var k2) = unifyVar k1 k2
>     unify (Var k1) t = bindVar k1 t
>     unify t (Var k2) = bindVar k2 t
>     unify t1 t2 = undefined
>         
