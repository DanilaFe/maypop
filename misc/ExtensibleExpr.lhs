We're going to need quite a few language extensions for this.

> {-# LANGUAGE TypeFamilies #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE QuantifiedConstraints #-}

I'll be using `liftA2` frequently, so here that is.

> import Control.Applicative

These are some tools for type-level programming.
I'll be creating "wrapper" functors that introduce
language features (`Nums` introduces numbers, `Bools` introduces
booleans), but I want a "lower" functor to be able to refer
to expressions "above" it. For this, we need a structure
like `Nums (Bools (Nums (Bools ...)))`, which is exactly
what `Fix` defines. `Compose` is the composition of two functors.

> newtype Fix f = Fix (f (Fix f))
> newtype Compose g f a = Comp (g (f a))

We now define a typeclass `Eval`, which says that
an expression type `a` can be evaluated in a monadic
context `m` into some value type `v`.

> class Monad m => Eval a m v where
>     eval :: a -> m v
>
> instance Eval (g (f a)) m v => Eval (Compose g f a) m v where
>     eval (Comp g) = eval g

Since numbers and booleans work on stuff that "can be converted"
to and from numbers and booleans, and since we want to keep
this as general as possible to allow various value types,
we define a general typeclass for "stuff that can be converted to and from a different type".
Additionally, the `lift` function uses `from` and `to` while preserving
the same value type `v`, which helps us fight ambiguity in later
typeclass definitions.

> class Conv v t where
>     from :: t -> v
>     to :: v -> Maybe t
> 
>     lift :: (t -> t -> t) -> v -> v -> Maybe v
>     lift f l r = from <$> liftA2 f (to l) (to r)

And now, the first of our functors. Notice that
`Nums` does not recursively refer to itself (because
it may actually be referring to some other type of expression).
The recursion is taken care of by `Fix`.

> data Nums a = N Int | Plus a a | NumNext a

As long as the expression type that `Nums` is wrapping can be evaluated,
and the value type can be converted to and from and integer, we can evaluate
`Nums` in any monadic context that supports failure (evaluation fails when adding non-integers).

> instance (Eval a m v, MonadFail m, Conv v Int) => Eval (Nums a) m v where
>     eval (N i) = pure $ from i
>     eval (Plus l r) = liftA2 (lift ((+) :: Int -> Int -> Int)) (eval l) (eval r) >>= maybe (fail "Couldn't add non-integers.") return
>     eval (NumNext a) = eval a

A similar idea applies to `Bools`.

> data Bools a = B Bool | And a a | BoolNext a
> 
> instance (Eq v, Eval a m v, MonadFail m, Conv v Bool) => Eval (Bools a) m v where
>     eval (B b) = pure $ from b
>     eval (And l r) = liftA2 (lift (&&)) (eval l) (eval r) >>= maybe (fail "Couldn't compare non-booleans.") return
>     eval (BoolNext a) = eval a

Now, we'd benefit from a value that can be both an integer and a boolean (since ideally
we'd like to be able to compose `Nums` and `Bools` to create a single expression type
with _both_ numbers and booleans).

> data Value = IntVal Int | BoolVal Bool deriving (Eq, Show)
> 
> instance ((forall a. Eval a m v => Eval (f a) m v), Monad m) => Eval (Fix f) m v where
>     eval (Fix f) = eval f
> 
> instance Conv Value Int where
>     from = IntVal
>     
>     to (IntVal i) = Just i 
>     to _ = Nothing
> 
> instance Conv Value Bool where
>     from = BoolVal
> 
>     to (BoolVal b) = Just b
>     to _ = Nothing

Here's how we can write down various expressions.

The first is a numeric-only expression:

> ex1 :: Fix Nums
> ex1 = Fix (Plus (Fix (N 1)) (Fix (N 2)))

We can run it like so (we use `Maybe` as an instance of `MonadFail`):

> run1 :: Maybe Value
> run1 = eval ex1

The second is a boolean-only expression:

> ex2 :: Fix Bools
> ex2 = Fix (And (Fix (B True)) (Fix (B False)))

It's evaluated the same way:

> run2 :: Maybe Value
> run2 = eval ex2

And here's a boolean-and-number expression:

> ex3 :: Fix (Compose Nums Bools)
> ex3 = Fix $ Comp $ NumNext $ And (Fix $ Comp $ NumNext $ (B True)) (Fix $ Comp $ NumNext $ (B False))

Like the two before it, it can trivially be evaluated.

> run3 :: Maybe Value
> run3 = eval ex3
