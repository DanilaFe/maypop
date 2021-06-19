module Data.Nat
import Logic (Eq(..), cong, replace, sym)

data Nat : Type 0 where
    O : Nat
    S (n : Nat) : Nat

plus : Nat -> Nat -> Nat
plus n m =
    match n as x in Nat _ return Nat with
        O -> m
        S nn -> S (plus nn m)

plus_O_n : forall (n : Nat). Eq Nat (plus O n) n
plus_O_n n = Refl Nat n

plus_n_O : forall (n : Nat). Eq Nat (plus n O) n
plus_n_O n =
    match n as x in Nat _ return Eq Nat (plus x O) x with
        O -> Refl Nat O
        S nn -> cong Nat Nat S (plus nn O) nn (plus_n_O nn)

plus_S : forall (n m : Nat). Eq Nat (S (plus n m)) (plus n (S m))
plus_S n m =
    match n as x in Nat _ return Eq Nat (S (plus x m)) (plus x (S m)) with
        O -> Refl Nat (S m)
        S nn -> cong Nat Nat S (S (plus nn m)) (plus nn (S m)) (plus_S nn m)

plus_comm : forall (n m : Nat). Eq Nat (plus n m) (plus m n)
plus_comm n m =
    match m as x in Nat _ return Eq Nat (plus n x) (plus x n) with
        O -> plus_n_O n
        S mm -> replace Nat (\(p : Nat). Eq Nat p (S (plus mm n))) (S (plus n mm)) (plus n (S mm)) (plus_S n mm) (cong Nat Nat S (plus n mm) (plus mm n) (plus_comm n mm))

times : Nat -> Nat -> Nat
times n m =
    match n as _ in Nat _ return Nat with
        O -> O
        S nn -> plus m (times nn m)

times_O_n : forall (n : Nat). Eq Nat (times O n) O
times_O_n n = Refl Nat O

times_S_n : forall (n : Nat). Eq Nat (times (S O) n) n
times_S_n n = plus_n_O n
