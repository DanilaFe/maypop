In this module, we'll define a small but useful construct: an infinite list.
It frequently happens that we need an inexhaustible supply of _something_.
When pretty printing an expression, we need an infinite supply of names
that can be assigned to DeBrujin indices; when we perform unification,
we need an infinite supply of fresh unifiction variables. 

> {-# LANGUAGE DeriveFunctor #-}
> {-# LANGUAGE FlexibleInstances #-}
> module Language.Maypop.InfiniteList where

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
