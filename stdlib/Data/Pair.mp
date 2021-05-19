module Data.Pair

data Pair (A B : Type 0): Type 0 where
| MkPair (x : A) (y : B) : Pair
end

fst : forall (A B : Type 0). Pair A B -> A where
fst t1 t2 p =
    match p as x in Pair _ return t1 with
    | MkPair x y -> x
    end
end

snd : forall (A B : Type 0). Pair A B -> B where
snd t1 t2 p =
    match p as x in Pair _ return t2 with
    | MkPair x y -> y
    end
end

swap : forall (A B : Type 0). Pair A B -> Pair B A where
swap t1 t2 p =
    match p as x in Pair _ return Pair t2 t1 with
    | MkPair x y -> MkPair t2 t1 y x
    end
end

curry : forall (A B : Type 0). forall (C : Type 0).
        (Pair A B -> C) -> A -> B -> C where
curry ta tb tc f a b = f (MkPair ta tb a b)
end

uncurry : forall (A B : Type 0). forall (C : Type 0).
          (A -> B -> C) -> Pair A B -> C where
uncurry ta tb tc f p =
    match p as x in Pair _ return tc with
    | MkPair x y -> f x y
    end
end
