In this module, we'll cover evaluating Maypop terms.

> module Language.Maypop.Eval where
> import Language.Maypop.Syntax
> import Control.Monad
> import Data.Bifunctor
> import Data.Maybe
> import Data.Void

We'll go with normal-order evaluation. Lazy evaluation would
require some degree of sharing, which would be a little
bit of a pain to implement, but applicative order evaluation
would make it had to define control structures like `if/else`.
In normal-order evaluation, we reduce the leftmost, outermost
redex. This means that function arguments are substituted into
a function before they are evaluated.

Our calculus of constructions is expanded with data types and global
function definitions (which are imported from modules),
which means that we have the following types of reduction

* __\\(\\beta\\)-reduction__: the classic type of reduction, which consists
of the substitution of an argument into a lambda abstraction's body.
For example, \\((\\lambda x. x) y \\mapsto y\\) is an instance of this
type of reduction.
* __\\(\\delta\\)-reduction__: this type of reduction will replace
global variables with their definitions. The substitution \\(\\text{id}\\mapsto \\lambda x.x\\)
is an instance of this type of reduction.
* __\\(\\zeta\\)-reduction__: this type of reduction is used for `let`
expressions. For example, we may have \\(\\textbf{let}\\ x = (1+2)\\ \\textbf{in}\\ x+1 \\mapsto (1+2)+1\\).
* __\\(\\iota\\)-reduction__: this final type of reduction is used to eliminate
case expressions. It is a little long to write out, but it essentially
allows case expressions to "unpack" instances of constructed terms and
use their contents.

> eval :: ParamTerm a -> ParamTerm a
> eval (Fun f) = eval $ absurd <$> (foldr Abs (fBody f) (fArity f)) -- Delta reduction
> eval (Abs l r) = Abs (eval l) (eval r)
> eval (App l r) = case eval l of
>     (Abs _ b) -> eval $ substitute 0 r b -- Beta reduction
>     t -> App t (eval r)
> eval (Let l r) = do
>     let l' = eval l
>     eval $ substitute 0 l' r -- Zeta reduction
> eval (Prod l r) = Prod (eval l) (eval r)
> eval c@(Case t i tt ts) = fromMaybe c $ do -- Iota reduction
>     ((i', ci), xs) <- collectConstrApps (eval t)
>     guard $ i == i'
>     b <- nth ci ts
>     return $ eval $ substituteMany 0 (drop (length $ iParams i) xs) b
> eval t = t
>
> collectConstrApps :: ParamTerm a -> Maybe ((Inductive, Int), [ParamTerm a])
> collectConstrApps t = second reverse <$> collect t
>     where
>         collect (App l r) = second (r:) <$> collect l
>         collect (Constr i ci) = Just ((i, ci), [])
>         collect _ = Nothing
