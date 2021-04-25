> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE AllowAmbiguousTypes #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE FunctionalDependencies #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE GeneralizedNewtypeDeriving #-}
> module Language.Maypop.Unification where
>
> class Monad m => MonadUnify k v m | m -> k, m -> v where
>     fresh :: m k
>     bind :: k -> v -> m ()
>     merge :: k -> k -> m ()
