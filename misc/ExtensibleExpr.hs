{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE QuantifiedConstraints #-}

import Data.Void
import Control.Applicative

newtype Fix f = Fix (f (Fix f))
newtype Compose g f a = Comp (g (f a))

class Monad m => Eval a m v where
    eval :: a -> m v

instance Monad m => Eval Void m v where
    eval = absurd

class Conv v t where
    from :: t -> v
    to :: v -> Maybe t

    lift :: (t -> t -> t) -> v -> v -> Maybe v
    lift f l r = from <$> liftA2 f (to l) (to r)

data Nums a = N Int | Plus a a | NumNext a

instance (Eval a m v, MonadFail m, Conv v Int) => Eval (Nums a) m v where
    eval (N i) = pure $ from i
    eval (Plus l r) = liftA2 (lift ((+) :: Int -> Int -> Int)) (eval l) (eval r) >>= maybe (fail "Couldn't add non-integers.") return
    eval (NumNext a) = eval a

data Bools a = B Bool | And a a | BoolNext a

instance (Eq v, Eval a m v, MonadFail m, Conv v Bool) => Eval (Bools a) m v where
    eval (B b) = pure $ from b
    eval (And l r) = liftA2 (lift (&&)) (eval l) (eval r) >>= maybe (fail "Couldn't compare non-booleans.") return
    eval (BoolNext a) = eval a

data Value = IntVal Int | BoolVal Bool deriving (Eq, Show)

instance ((forall a. Eval a m v => Eval (f a) m v), Monad m) => Eval (Fix f) m v where
    eval (Fix f) = eval f

instance Conv Value Int where
    from = IntVal
    
    to (IntVal i) = Just i 
    to _ = Nothing

instance Conv Value Bool where
    from = BoolVal

    to (BoolVal b) = Just b
    to _ = Nothing

ex1 :: Fix Nums
ex1 = Fix (Plus (Fix (N 1)) (Fix (N 2)))

run1 :: Maybe Value
run1 = eval ex1

ex2 :: Fix Bools
ex2 = Fix (And (Fix (B True)) (Fix (B False)))

run2 :: Maybe Value
run2 = eval ex2

ex3 :: Fix (Compose Nums Bools)
ex3 = Fix $ Comp $ NumNext $ And (Fix $ Comp $ NumNext $ (B True)) (Fix $ Comp $ NumNext $ (B False))
