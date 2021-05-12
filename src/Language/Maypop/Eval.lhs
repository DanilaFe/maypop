In this module, we'll cover evaluating Maypop terms.

> module Language.Maypop.Eval where
> import Language.Maypop.Syntax
> import Control.Monad
> import Data.Bifunctor
> import Data.Maybe

We'll go with normal-order evaluation. Lazy evaluation would
require some degree of sharing, which would be a little
bit of a pain to implement, but applicative order evaluation
would make it had to define control structures like `if/else`.
In normal-order evaluation, we reduce the leftmost, outermost
redex. This means that function arguments are substituted into
a function before they are evaluated.

> eval :: ParamTerm a -> ParamTerm a
> eval (Abs l r) = Abs (eval l) (eval r)
> eval (App l r) = case eval l of
>     (Abs _ b) -> eval $ substitute 0 r b
>     t -> App t (eval r)
> eval (Let l r) = do
>     let l' = eval l
>     eval $ substitute 0 l' r
> eval (Prod l r) = Prod (eval l) (eval r)
> eval c@(Case t i _ ts) = fromMaybe c $ do
>     ((i', ci), xs) <- collectConstrApps (eval t)
>     guard $ i == i'
>     b <- nth ci ts
>     return $ eval $ substituteMany 0 xs b
> eval t = t

> collectConstrApps :: ParamTerm a -> Maybe ((Inductive, Int), [ParamTerm a])
> collectConstrApps t = second reverse <$> collect t
>     where
>         collect (App l r) = second (r:) <$> collect l
>         collect (Constr i ci) = Just ((i, ci), [])
>         collect _ = Nothing
