module Data.Nat
import Logic (Eq(..), cong)

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
