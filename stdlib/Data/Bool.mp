module Data.Bool

data Bool : Type 0 where
    True : Bool
    False : Bool

and : forall (a : Bool). forall (b : Bool). Bool
and a b =
    match a as x in Bool _ return Bool with
        True -> b
        False -> False

or : forall (a : Bool). forall (b : Bool). Bool
or a b =
    match a as x in Bool _ return Bool with
        True -> True
        False -> b
