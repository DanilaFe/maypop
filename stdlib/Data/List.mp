module Data.List

data List (A : Type 0): Type 0 where
    Nil : List 
    Cons (x : A) (xs : List A) : List

concat : forall (A : Type 0). List A -> List A -> List A
concat t1 l1 l2 =
    match l1 as _ in List _ return List t1 with
        Nil -> l2
        Cons x xs -> Cons t1 x (concat t1 xs l2)

map : forall (A : Type 0). forall (B: Type 0). (A -> B) -> List A -> List B
map t1 t2 f l =
    match l as _ in List _ return List t2 with
        Nil -> Nil t2
        Cons x xs -> Cons t2 (f x) (map t1 t2 f xs)

foldr : forall (A B : Type 0). (A -> B -> B) -> B -> List A -> B
foldr t1 t2 f b l =
    match l as _ in List _ return t2 with
        Nil -> b
        Cons x xs -> f x (foldr t1 t2 f b xs)
