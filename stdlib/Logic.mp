module Logic

data False : Prop where

data And (A B : Prop) : Prop where
    Both (a : A) (b : B) : And

data Or (A B : Prop) : Prop where
    Left (a : A) : Or
    Right (b : B) : Or

Not : Prop -> Prop
Not p = p -> False

andOr : forall (A B : Prop). And A B -> Or A B
andOr A B a =
    match a as x in And _ return Or A B with
        Both a b -> Left A B a

data Eq (A : Type 0) (x : A) : A -> Prop where
    Refl : Eq x

eqDec : Type 0 -> Prop
eqDec t = forall (a : t). forall (b : t). Or (Eq t a b) (Not (Eq t a b))

replace : forall (A : Type 0). forall (P : A -> Prop).
          forall (x : A). forall (y : A).
          Eq A x y -> P x -> P y
replace t P x y eq Px =
    match eq as e in Eq _ z return P z with
        Refl -> Px

cong : forall (A B : Type 0). forall (C : A -> B).
       forall (x y : A). Eq A x y -> Eq B (C x) (C y)
cong t1 t2 C x y eq =
    match eq as _ in Eq _ z return Eq t2 (C x) (C z) with
        Refl -> Refl t2 (C x)

sym : forall (A : Type 0). forall (x y : A). Eq A x y -> Eq A y x
sym t x y eq =
    match eq as _ in Eq _ z return Eq t z x with
        Refl -> Refl t x
