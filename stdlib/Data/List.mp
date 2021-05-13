module Data.List

{-
data List (A : Type 0): Type 0 where
    | Nil : List 
    | Cons (x : A) (List A) : List
end

concat : forall (A : Type 0). forall (l1 : List A). forall (l2 : List A). List A where
concat t1 t2 l1 l2 = match l1 as x in List _ return t1 with
    | Nil -> l2
    | Cons x l3 -> Cons x (concat l3 l2)
    end
end

-- TODO: Check signature of map
-- TODO: Maybe write a "porting guide" for types from Haskell/Idris to Maypop
map : forall (A : Type 0). forall (B: Type 0). forall (l1 : List A). forall (F : forall (x:A). B). List B where
map t1 t2 t3 t4 l f = match l as x in List _ return List B with
    | Nil -> Nil
    | Cons x l2 = Cons (f x) (map l2 f)
    end
end

-- TODO: Fix fold type signature
-- fold : forall (A : Type 0). forall (B : Type 0). forall (l1 : List A). forall (F : forall (x:A). forall (y:A). B). List B.
-}
