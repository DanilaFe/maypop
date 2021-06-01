module Class.Eq
import Data.Bool (Bool(..), not)

data Eq (A : Type 0) : Constraint where
| MkEq (f : A -> A -> Bool) : Eq
end

eq : forall (A : Type 0). Eq A -> A -> A -> Bool where
eq t e a b =
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
