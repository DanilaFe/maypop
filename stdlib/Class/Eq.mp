module Class.Eq
import Data.Bool (Bool(..), not, and)
import Data.Nat (Nat(..))
import Data.Pair (Pair(..))

data Eq (A : Type 0) : Constraint where
| MkEq (f : A -> A -> Bool) : Eq
end

eq : forall (A : Type 0). Eq A -> A -> A -> Bool where
eq {t} {e} a b =
    match e as _ in Eq _ return Bool with
    | MkEq f -> f a b
    end
end

eqBool : Eq Bool where
eqBool = MkEq Bool (\(a b : Bool).
    match a as _ in Bool _ return Bool with
    | True -> b
    | False -> not b
    end)
end

natEq : Nat -> Nat -> Bool where
natEq a b =
    match a as _ in Nat _ return Bool with
    | O ->
        match b as _ in Nat _ return Bool with
        | O -> True
        | S bb -> False
        end
    | S aa -> 
        match b as _ in Nat _ return Bool with
        | O -> False
        | S bb -> natEq aa bb
        end
    end
end

eqNat : Eq Nat where
eqNat = MkEq Nat natEq
end

pairEq : forall (A B : Type 0). Eq A -> Eq B -> Pair A B -> Pair A B -> Bool where
pairEq {t1} {t2} {e1} {e2} p1 p2 =
    match p1 as _ in Pair _ return Bool with
    | MkPair p1a p1b ->
        match p2 as _ in Pair _ return Bool with
        | MkPair p2a p2b -> and (eq p1a p2a) (eq p1b p2b)
        end
    end
end

eqPair : forall (A B : Type 0). Eq A -> Eq B -> Pair A B -> Pair A B -> Bool where
eqPair {t1} {t2} {e1} {e2} = pairEq
end
