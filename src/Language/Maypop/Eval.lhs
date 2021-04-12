In this module, we'll cover evaluating Maypop terms.

> module Language.Maypop.Eval where
> import Language.Maypop.Syntax

We'll go with normal-order evaluation. Lazy evaluation would
require some degree of sharing, which would be a little
bit of a pain to implement, but applicative order evaluation
would make it had to define control structures like `if/else`.
In normal-order evaluation, we reduce the leftmost, outermost
redex. This means that function arguments are substituted into
a function before they are evaluated.

> eval :: Term -> Term
> eval (Abs l r) = Abs (eval l) (eval r)
> eval (App l r)
>     | (Abs _ b) <- offsetFree (-1) (eval l) = eval $ substitute 0 r b
>     | t <- eval l = App t (eval r)
> eval (Prod l r) = Prod (eval l) (eval r)
> eval t = t
