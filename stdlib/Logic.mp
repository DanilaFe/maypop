module Logic

data False : Prop where
end

data And (A : Prop) (B : Prop) : Prop where
| Both (a : A) (b : B) : And
end

data Or (A : Prop) (B : Prop) : Prop where
| Left (a : A) : Or
| Right (b : B) : Or
end

Not : Prop -> Prop where
Not p = p -> False
end

andOr : forall (A : Prop). forall (B : Prop).
        And A B -> Or A B where
andOr A B a =
    match a as x in And _ return Or A B with
    | Both a b -> Left A B a
    end
end

data Eq (A : Type 0) (x : A) : A -> Prop where
| Refl : Eq x
end

eqDec : Type 0 -> Prop where
eqDec t = forall (a : t). forall (b : t). Or (Eq t a b) (Not (Eq t a b))
end

replace : forall (A : Type 0). forall (P : A -> Prop).
          forall (x : A). forall (y : A).
          Eq A x y -> P x -> P y where
replace t P x y eq Px =
    match eq as e in Eq _ z return P z with
    | Refl -> Px
    end
end
