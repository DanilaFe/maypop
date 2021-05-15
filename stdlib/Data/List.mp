module Data.List

data List (A : Type 0): Type 0 where
    | Nil : List 
    | Cons (x : A) (xs : List A) : List
end

concat : forall (A : Type 0). List A -> List A -> List A where
concat t1 l1 l2 = match l1 as _ in List _ return List t1 with
    | Nil -> l2
    | Cons x xs -> Cons t1 x (concat t1 xs l2)
    end
end

map : forall (A : Type 0). forall (B: Type 0). (A -> B) -> List A -> List B where
map t1 t2 f l = match l as _ in List _ return List t2 with
    | Nil -> Nil t2
    | Cons x xs -> Cons t2 (f x) (map t1 t2 f xs)
    end
end

-- TODO: Fix fold type signature
-- fold : forall (A : Type 0). forall (B : Type 0). forall (l1 : List A). forall (F : forall (x:A). forall (y:A). B). List B.
