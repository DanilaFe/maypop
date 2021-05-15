module Prelude
import Data.List (List(..), concat, map)
import Data.Pair (Pair(..), fst, snd, swap, curry, uncurry)
import Data.Void (Void, absurd)
import Data.Nat (Nat(..), plus)
import Logic (And(..), Or(..), Not, Eq(..), replace)

list1 : List Nat where
list1 = Cons Nat (S (S (S O))) (Cons Nat (S (S O)) (Nil Nat))
end

list2 : List Nat where
list2 = Cons Nat (S (S (S (S (S (S O)))))) (Nil Nat)
end

list3 : List Nat where
list3 = concat Nat list1 list2
end

list4 : List Nat where
list4 = map Nat Nat (plus (S O)) list3
end

main : List Nat where
main = list4
end
