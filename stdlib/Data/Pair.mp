module Data.Pair

data Pair (A B : Type 0): Type 0 where
    MkPair (x : A) (y : B) : Pair

fst : forall (A B : Type 0). Pair A B -> A
fst {t1} {t2} p =
    match p as x in Pair _ return t1 with
        MkPair x y -> x

snd : forall (A B : Type 0). Pair A B -> B
snd {t1} {t2} p =
    match p as x in Pair _ return t2 with
        MkPair x y -> y

swap : forall (A B : Type 0). Pair A B -> Pair B A
swap {t1} {t2} p =
    match p as x in Pair _ return Pair t2 t1 with
        MkPair x y -> MkPair t2 t1 y x

curry : forall (A B : Type 0). forall (C : Type 0).
        (Pair A B -> C) -> A -> B -> C
curry {ta} {tb} {tc} f a b = f (MkPair ta tb a b)

uncurry : forall (A B : Type 0). forall (C : Type 0).
          (A -> B -> C) -> Pair A B -> C
uncurry {ta} {tb} {tc} f p =
    match p as x in Pair _ return tc with
        MkPair x y -> f x y
