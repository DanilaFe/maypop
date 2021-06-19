module Prelude
import Data.List (List(..), concat, map)
import Data.Nat (Nat(..), plus)
import Data.Pair (Pair(..), fst, snd, swap, curry, uncurry)
import Data.Void (Void, absurd)
import Data.Bool (Bool(..), and, or)
import Logic (And(..), Or(..), Not, Eq(..), replace)

list1 : List Nat
list1 = Cons Nat (S (S (S O))) (Cons Nat (S (S O)) (Nil Nat))

list2 : List Nat
list2 = Cons Nat (S (S (S (S (S (S O)))))) (Nil Nat)

list3 : List Nat
list3 = concat Nat list1 list2

list4 : List Nat
list4 = map Nat Nat (plus (S O)) list3

main : List Nat
main = list4
