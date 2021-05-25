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
> eval (Fun f) = eval $ expandFunction f
> eval (Abs l r) = Abs (eval l) (eval r)
> eval t@App{} = evalApps $ evalLeftmost t
> eval (Let l r) = do
>     let l' = eval l
>     eval $ substitute 0 l' r -- Zeta reduction
> eval (Prod l r) = Prod (eval l) (eval r)
> eval (Case t i tt ts) = fromMaybe (Case (eval t) i (eval tt) (map eval ts)) $ do -- Iota reduction (case)
>     ((i', ci), xs) <- collectConstrApps (eval t)
>     guard $ i == i'
>     b <- nth ci ts
>     return $ eval $ substituteMany 0 (drop (length $ iParams i) xs) b
> eval t = t

This uses a little helper function, `expandFunction`, which converts
functions from their `f x = t` form into something like `\x -> t`. Function
terms do not have parameters in them, so we use `fmap absurd` to convert
from `ParamTerm Void` to `ParamTerm a`.

> expandFunction :: Function -> ParamTerm a
> expandFunction f = absurd <$> foldr Abs (fBody f) (map snd $ fArity f)

You may notice that the case for `App` uses a whole another function. Indeed,
the situation with applications is a little complicated. Of course, there's
the "basic" case of \\(\\beta\\)-reduction: if the left term evaluates to
a lambda abstraction, we substitute the right term in. But \\(\\iota\\)-reduction
can also be applied here; fixpoint definition are __not subject to \\(\\delta\\)-reduction__
(because we can cause infinite substitutions this way), and are only expanded when
their decreasing argument evaluates to a constructor (and its parameters). But
the decreasing parameter of a fixpoint function can be its 10th, 20th, or even 100th parameter!
We must therefore collect all application arguments (right terms) we encounter, and inspect
them if we come across a fixpoint.

The first step to perform all of this evaluation is to collect all of the terms
being applied to some argument on the left. We don't evaluate the terms just yet;
since we are going for normal-order reduction, we want to substitute the unevaluated
expressions into the function body. If we hit a "dead end" (a term that's not another
application), we make one more attempt: if the term on the left can be _evaluated_
to an application, we continue. Eventually, this function returns a list of arguments
and a normalized term they are applied to, which is
{{< sidenote "right" "function-note" "either an abstraction or a fixpoint function." >}}
It cannot be a non-fixpoint function, since we always expand those into their lambda
abstraction form whenever we come across them.
{{< /sidenote >}}

> evalLeftmost :: ParamTerm a -> (ParamTerm a, [ParamTerm a])
> evalLeftmost = second reverse . evalL
>     where
>         evalL (App l r) = second (r:) $ evalL l
>         evalL t =
>             case eval t of
>                 t'@App{} -> evalL t'
>                 t' -> (t', [])

Once we have this chain of applications collected, we try to actually
perform the application. If the term on the far left is a lambda abstraction,
we perform standard \\(\\beta\\)-reduction, try to normalize the result,
and continue our application. On the other hand, if the leftmost term
is a fixpoint function, we first try to see if enough arguments are applied
to it to contain the "decreasing" argument. If that's the case, we ensure
that this argument is a constructor application (guaranteed to be the _right_
type of constructor by typechecking). If it is, after all, a constructor,
we expand the fixpoint function into its lambda abstraction form and attempt
evaluation again.

In all other cases (non-abstraction, fixpoint with too
few arguments, fixpoint with non-constructor argument) we simply rebuild
the chain of applications, but this time evaluating the arguments.

{{< todo >}}We probably want to re-try evalLeftmost here, since the lambda's body can contain a partially applied fixpoint function whose decreasing argument is within ts{{< /todo >}}

> evalApps :: (ParamTerm a, [ParamTerm a]) -> ParamTerm a
> evalApps (Abs _ b, t:ts) = evalApps (eval $ substitute 0 t b, ts) -- Beta reduction
> evalApps (Fix f, ts)
>     | Just t <- nth (fxDecArg f) ts
>     , Just t' <- fmap rebuildConstrApps $ collectConstrApps $ eval t =
>         evalApps $ (expandFunction (fxFun f), replaceNth (fxDecArg f) t' ts) -- Iota reduction (fixpoint)
> evalApps (t, ts) = foldl App t (map eval ts)
>
> replaceNth :: Int -> a -> [a] -> [a]
> replaceNth _ _ [] = []
> replaceNth 0 x' (_:xs) = x' : xs
> replaceNth n x' (x:xs) = x : replaceNth (n-1) x' xs
> 
> collectConstrApps :: ParamTerm a -> Maybe ((Inductive, Int), [ParamTerm a])
> collectConstrApps t = second reverse <$> collect t
>     where
>         collect (App l r) = second (r:) <$> collect l
>         collect (Constr i ci) = Just ((i, ci), [])
>         collect _ = Nothing
>
> rebuildConstrApps :: ((Inductive, Int), [ParamTerm a]) -> ParamTerm a
> rebuildConstrApps ((i, ci), ts) = foldl App (Constr i ci) ts
