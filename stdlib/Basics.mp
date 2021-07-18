module Basics

id : forall (a : Type 0). a -> a
id {t} x = x
