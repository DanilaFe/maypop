module Data.Void

data Void : Type 0 where

absurd : forall (A : Type 0). forall (v : Void). A
absurd t v =
    match v as x in Void _ return t with
