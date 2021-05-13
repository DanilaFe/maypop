module Data.Void

data Void : Type 0 where
end

absurd : forall (A : Type 0). forall (v : Void). A where
absurd t v =
    match v as x in Void _ return t with
    end
end
