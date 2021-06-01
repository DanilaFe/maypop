module Data.Bool

data Bool : Type 0 where
    | True : Bool
    | False : Bool
end 

and : forall (a : Bool). forall (b : Bool). Bool where
and a b =
    match a as x in Bool _ return Bool with
    | True -> b
    | False -> False
    end
end

or : forall (a : Bool). forall (b : Bool). Bool where
or a b =
    match a as x in Bool _ return Bool with
    | True -> True
    | False -> b
    end 
end

not : Bool -> Bool where
not b =
    match b as _ in Bool _ return Bool with
    | True -> False
    | False -> True
    end
end
