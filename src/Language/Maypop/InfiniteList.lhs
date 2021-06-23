In this module, we'll define a small but useful construct: an infinite list.
It frequently happens that we need an inexhaustible supply of _something_.
When pretty printing an expression, we need an infinite supply of names
that can be assigned to DeBrujin indices; when we perform unification,
we need an infinite supply of fresh unifiction variables. 

> {-# LANGUAGE DeriveFunctor #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FunctionalDependencies #-}
> {-# LANGUAGE GeneralizedNewtypeDeriving #-}
> {-# LANGUAGE UndecidableInstances #-}
> module Language.Maypop.InfiniteList where
> import Control.Monad.State
> import Control.Monad.Identity
> import Control.Monad.Reader
> import Control.Monad.Except
> import Control.Applicative

The definition of an `InfList` is extremely simple. It's just a list
without a base case! Thanks to Haskell's lazy evaluation, this
is a perfectly valid data type, and behaves exactly like we want.

> data InfList a = Cons a (InfList a) deriving Functor

It's nice to be able to construct (the beginning of) an infinite list
from a "regular" list. That's easy enough:

> fromList :: [a] -> InfList a -> InfList a
> fromList xs ns = foldr Cons ns xs

We also want to be able to transform a single element of this list
into many elements (we use this to build up longer and longer names
as we run out of short ones).

> expand :: (a -> [a]) -> InfList a -> InfList a
> expand f (Cons x xs) = fromList (f x) (expand f xs)

Finally, we need ways to get the current head (next element) and the current tail (the rest of the elements).
Unlike those for list, these functions are guaranteed to be safe, since we can never exhaust our
infinite list.

> headInf :: InfList a -> a
> headInf (Cons x _) = x
>
> tailInf :: InfList a -> InfList a
> tailInf (Cons _ xs) = xs

For most types, there's a fairly straightforward way for 
creating an infinite list of that type. Let's define a typeclass
for such types:

> class Infinite a where
>     infList :: InfList a

One instance of this typelcass is for the `String` type. Although
there are multiple ways of generating an infinite list of strings,
a simple one is to use a method similar to that used by Haskell
and its type parameters: we start with "a", "b", and so on,
and move on to "aa", "ab", etc.. Eventually, we will
start returning strings of 3 characters, then of four, and so on.
Let's write this down:

> instance Infinite [Char] where
>     infList = fromList alphabet $ expand ((<$>alphabet) . (++)) infList
>         where alphabet = map return ['a'..'z']

The main use of an infinite list is to pull items from it for other uses.
In a sense, this is a stateful operation: we obviously can't modify
an `InfList` object, so we have to keep track of its last version. To pull
a new element, we look at the current version's head, and update the current
version to refer to the tail. In the style of the MTL, we define a typeclass
that encapsulates this functionality:

> class Monad m => MonadInf k m | m -> k where
>     pop :: m k
>
>     popN :: Int -> m [k]
>     popN = (`replicateM` pop)

Also in the style of the MTL, we define a monad trasnformer that is an instance
of our new type class. Let's call it `InfT`. This monad transformer is simply
a `newtype` over a `StateT` monad; we do not, however, make `InfT` an instance
of `MonadState`, to allow other library code to combine `InfT` with its own
state as needed.

> newtype InfT k m a = MkInfT { unwrapInfT :: StateT (InfList k) m a }
>     deriving (Functor, Applicative, Monad, MonadTrans, Alternative, MonadPlus, MonadReader r)

The implementation of the `pop` operation is pretty the same as what we
described above.

> instance Monad m => MonadInf k (InfT k m) where
>     pop = MkInfT $ gets headInf <* modify tailInf

Frustratingly, we also need to mechanically implement a handful of `MonadInf`
instances for some common built-in trasnformers.

> instance MonadInf k m => MonadInf k (ReaderT r m) where
>     pop = lift pop
>
> instance MonadInf k m => MonadInf k (StateT s m) where
>     pop = lift pop
>
> instance MonadInf k m => MonadInf k (ExceptT e m) where
>     pop = lift pop

As usual, we need a way to run the computation represented by `InfT`, returning
a computation in the underlying monad `m`. Since `InfT` is effectively an alias
for `StateT`, our new function merely invokes `runStateT`, and cleans up
by throwing away the unused remainder of the infinite list.

> runInfT :: (Infinite k, Monad m) => InfT k m a -> m a
> runInfT m = fst <$> runStateT (unwrapInfT m) infList

For the trivial case in which there _is_ no underlying computation, we define
a type alias `Inf`, and a corresponding `runInf` function:

> type Inf k a = InfT k Identity a
>
> runInf :: (Infinite k) => Inf k a -> a
> runInf = runIdentity . runInfT
