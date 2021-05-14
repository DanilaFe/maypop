module Data.Nat

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
