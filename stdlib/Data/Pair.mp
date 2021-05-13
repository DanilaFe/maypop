module Data.Pair

data Pair (A : Type 0) (B : Type 0): Type 0 where
| MkPair (x : A) (y : B) : Pair
end

fst : forall (A : Type 0). forall (B : Type 0). forall (p : Pair A B). A where
fst t1 t2 p =
    match p as x in Pair _ return t1 with
    | MkPair x y -> x
    end
end

snd : forall (A : Type 0). forall (B : Type 0). forall (p : Pair A B). B where
snd t1 t2 p =
    match p as x in Pair _ return t2 with
    | MkPair x y -> y
    end
end

swap : forall (A : Type 0). forall (B : Type 0). forall (p : Pair A B). Pair B A where
swap t1 t2 p =
    match p as x in Pair _ return Pair t2 t1 with
    | MkPair x y -> MkPair t2 t1 y x
    end
end

curry : forall (A : Type 0). forall (B : Type 0). forall (C : Type 0).
        forall (f : forall (p : Pair A B). C). forall (a : A). forall (b : B). C where
curry ta tb tc f a b = f (MkPair ta tb a b)
end

uncurry : forall (A : Type 0). forall (B : Type 0). forall (C : Type 0).
          forall (f : forall (a : A). forall (b : B). C).
          forall (p : Pair A B). C where
uncurry ta tb tc f p =
    match p as x in Pair _ return tc with
    | MkPair x y -> f x y
    end
end
