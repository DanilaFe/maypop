> module Language.Maypop.InfiniteList where

> data InfList a = Cons a (InfList a)

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
