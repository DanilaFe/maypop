data Bool : Type 0 where
    | T : Bool
    |F : Bool
end 

and : forall (a b : Bool). Bool where
and a b = match a as x in Bool _ return a with
    | T -> match b  as y in Bool _ return b with 
        T -> T
        F -> F
    | F -> F 
    end
end

or : forall (a b : Bool). Bool where
or a b = match a as x in Bool _ return a with
    | T -> T
    | F -> b
    end 
end
