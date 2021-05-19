module Data.Nat
import Logic (Eq(..), cong, replace, sym)

data Nat : Type 0 where
| O : Nat
| S (n : Nat) : Nat
end

plus : Nat -> Nat -> Nat where
plus n m =
    match n as x in Nat _ return Nat with
    | O -> m
    | S nn -> S (plus nn m)
    end
end

plus_O_n : forall (n : Nat). Eq Nat (plus O n) n where
plus_O_n n = Refl Nat n
end

plus_n_O : forall (n : Nat). Eq Nat (plus n O) n where
plus_n_O n =
    match n as x in Nat _ return Eq Nat (plus x O) x with
    | O -> Refl Nat O
    | S nn -> cong Nat Nat S (plus nn O) nn (plus_n_O nn)
    end
end

plus_S : forall (n m : Nat). Eq Nat (S (plus n m)) (plus n (S m)) where
plus_S n m =
    match n as x in Nat _ return Eq Nat (S (plus x m)) (plus x (S m)) with
    | O -> Refl Nat (S m)
    | S nn -> cong Nat Nat S (S (plus nn m)) (plus nn (S m)) (plus_S nn m)
    end
end

plus_comm : forall (n m : Nat). Eq Nat (plus n m) (plus m n) where
plus_comm n m =
    match m as x in Nat _ return Eq Nat (plus n x) (plus x n) with
    | O -> plus_n_O n
    | S mm -> replace Nat (\(p : Nat). Eq Nat p (S (plus mm n))) (S (plus n mm)) (plus n (S mm)) (plus_S n mm) (cong Nat Nat S (plus n mm) (plus mm n) (plus_comm n mm))
    end
end
