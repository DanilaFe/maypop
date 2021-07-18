module Prelude
import Data.List (List(..), concat, map, foldr)
import Data.Nat (Nat(..), plus)
import Data.Pair (Pair(..), fst, snd, swap, curry, uncurry)
import Data.Void (Void, absurd)
import Data.Bool (Bool(..), and, or)
import Basics (id)
import Logic (And(..), Or(..), Not, Eq(..), replace)

list1 : List Nat
list1 = [3, 2 : Nat]

list2 : List Nat
list2 = [6 : Nat]

list3 : List Nat
list3 = concat list1 list2

list4 : List Nat
list4 = map (plus (S O)) list3

sum : List Nat -> Nat
sum = foldr plus 0

main : Nat
main = sum (map id list4)
