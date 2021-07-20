In this module, we convert parsed expressions into valid Maypop terms, by
resolving references to various variables to either their corresponding
function objects or their DeBrujin indices.

> {-# LANGUAGE RecursiveDo #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE MonoLocalBinds #-}
> module Language.Maypop.Resolver where
> import Prelude hiding (pi)
> import Language.Maypop.Syntax hiding (ParamTerm(..), Term)
> import qualified Language.Maypop.Syntax as S
> import Language.Maypop.Modules
> import Language.Maypop.Parser
> import Language.Maypop.Unification
> import Language.Maypop.Context
> import Language.Maypop.InfiniteList
> import Language.Maypop.Checking hiding (NotInductive)
> import Control.Applicative hiding ((<|>), many)
> import Control.Monad.Reader
> import Control.Monad.State
> import Control.Monad.Except
> import Text.Parsec
> import Text.Parsec.Token
> import Text.Parsec.Expr
> import Text.Parsec.Indent
> import qualified Data.Map as Map
> import qualified Data.Set as Set
> import Data.Char
> import Data.Monoid
> import Data.Bifunctor
> import Data.List
> import Data.Maybe
> import Data.Functor.Identity
> import Data.Either

Turning parsed expressions into their `Term` coutnerparts
can go wrong in many different ways. We first define a data
type to represent all the possible errors. Not in particular
the `InferError` constructor, which wraps a `TypeError`. Filling
in implicit arguments is based on types; we thus have to perform
type inference, which can itself yield a variety of errors.

> data ResolveError
>     = UnknownReference
>     | AmbiguousReference
>     | NotInductive
>     | InvalidArity
>     | IncompleteMatch
>     | ImportError ImportError
>     | InferError TypeError
>     | InvalidFixpoint
>     | InvalidResolve
>     deriving Show

An important concept in the Calculus of Inductive Constructions
is the notion of fixpoints. These are functions bundled with their
"decreasing" argument; we will need to track the "sizes" of the various
parameters to function calls so that we can determine the decreasing
argument, if any. We also use the `Self` size to avoid having to insert
`Fun` or `Ind` constructors referring to the current definition (for instance,
in recursive functions). That's not to say that inserting such recursive references
is impossible: recursive functions are invariably represented by cyclic data structures
in our representation. However, it's not immediately useful; more on that later.

> data VarSize = Self | Original | SmallerThan String | Unknown deriving Show

We also define a handy helper function that, if the current variable
is "smaller" than some other variable, returns that other variable.

> varParent :: VarSize -> Maybe String
> varParent (SmallerThan s) = Just s
> varParent _ = Nothing

We will not go straight from `ParseTerm` to `Term` while resolving. There is
another intermediate step: inserting "inferred" function arguments. For instance,
the parsed expression `id O` will first be translated to `id _ O` (inserting
a placeholder for the type we need to infer), and then be elaborated into
`id Nat O` after a round of type checking. To represent expressions
such as `id _ O`, we define a data type `ResolveParam`, which is used
to parameterize `ParamTerm`.

> data ResolveParam = SelfRef | Placeholder deriving (Eq, Show)
> type ResolveTerm = S.ParamTerm ResolveParam

In several places, it will be helpful to be aware of the current
definition that we are trying to resolve. For these situations,
we define `CurrentInd` and `CurrentFun`, which contain
useful information such as the types of the definition's parameters (and
posibly indices), as well as the definition's textual form (as `ParseInd`
or `ParseFun`).

> data CurrentInd = CurrentInd
>     { ciParams :: [S.Term]
>     , ciIndices :: [S.Term]
>     , ciParsed :: ParseInd
>     }
>
> data CurrentFun = CurrentFun
>     { cfParams :: [S.Term]
>     , cfParsed :: ParseFun
>     }

Another data type, `CurrentDef`, contains information that's common
to every definition. Note that instead of just having a `cdTerm`
field, which contains the term of the current definition, we have
`cdFutureTerm`. And indeed, if we think about it, that's exactly what it is:
we're in the middle of resolving a definition, so when we have a reference to it,
it's like we're holding something from the future in our hands. But how 
_can_ we have a reference to a term from the future? It's a bit out of scope
for this page, but check out [Csongor Kiss'](https://blog.csongor.co.uk/time-travel-in-haskell-for-dummies/) article
on the technique that allows this (time traveling!), and maybe also [this article of mine](https://danilafe.com/blog/haskell_lazy_evaluation/).

The main thing to know about handling such future values is that __we cannot make decisions based on them__.
This is because intuitively, we cannot base our decision based on its future outcone.
If this is too philosophical, you can think about what happens under the hood: our future
value is not actually a value, but a [thunk](https://wiki.haskell.org/Thunk). When time traveling, this thunk
contains a reference to itself. Then, To make a decision based on our future term,
we need to evaluate the thunk to a value. But the thunk contains itself, and
evaluating it requires making that decision, which once again requires evaluating
the thunk. We end up in an infinite loop. Sometimes, Haskell kindly lets us know
we've done so, and crashes with error message `<<loop>>`. Other times,
our program will simply hang. Neither outcome is desirable.

> data CurrentDef = CurrentDef
>     { cdFutureTerm :: S.Term
>     , cdType :: S.Term
>     , cdExtra :: Either CurrentInd CurrentFun
>     }

Now we have our various encodings of the current definition. Next, we move
on to defining the resolver's environment, which will be kept inside
a `Reader` monad. The reason we need an environment is that the translation
of the parsed term \\(x\\) depends on what surrounds it: 
if the whole expression is \\(\\lambda x. x\\), we translate \\(x\\)
to \\(0\\), yielding \\(\\lambda. 0\\). However, when the whole expression
is \\(\\lambda x. \\lambda y. x\\), we translate \\(x\\) to \\(1\\),
and the whole expression to \\(\\lambda.\\lambda.1\\). We thus keep
a stack of names associated with binders; when a name is on the top
of a stack, it was introduced last, and thus should be translated
to index \\(0\\); the second name from the top was introduced second-to-last,
and should thus be translated to index \\(1\\).

Another "dynamic" piece of data is `reApps`. Whereas `reVars` effectively
tracks the __binders__ around the current term, `reApps` tracks the
__applications__. Thus, in the expression \\(f\\ x\\ y\\), when we translate
\\(f\\), our `reApps` will include \\(x\\) and \\(y\\). We need this
to track decreasing arguments to functions: when we encounter a recursive
call, we check what arguments it's applied to, and record which, if any, are
smaller versions of the original arguments. Then, at the end, if we find
that one argument always receives a "smaller" argument, we know we're safe:
our function will eventually terminate. If, on the other hand, no argument
is consistently smaller, we will give up and report `InvalidFixpoint`.

The remaining two fields of our environment are `reHeader` (currently
only used to retrieve the current module name) and `reCurrentDef`,
the current definition data sturcutre we've define above.

> data ResolveEnv = ResolveEnv
>     { reVars :: [(String, VarSize)]
>     , reHeader :: ModuleHeader
>     , reCurrentDef :: Maybe CurrentDef
>     , reApps :: [ParseTerm]
>     }

Time for some functions that run a monadic computation `m a` in a modified `ResolveEnv`.
The first of these many functions is `withSizedVar`, which pushes a new variable
onto the stack, making it visible within the input computation, assigning to it
the index \\(0\\), and shifting the indices of the other variables' indices by one.
In addition to the variable name, this function also adds the variable's size information:
whether it's smaller, a recursive reference, or unknown.

> withSizedVar :: MonadReader ResolveEnv m => VarSize -> String -> m a -> m a
> withSizedVar vs s = local (\re -> re { reVars = (s,vs) : reVars re })

As a shortcut for the case when we are introducing a variable with no known
size information, we define `sizeVar` as follows:

> withVar :: MonadReader ResolveEnv m => String -> m a -> m a
> withVar = withSizedVar Unknown

Sometimes we need to introduce more than a single variable in the environment
at the same time (for instance, in case expression branches). We thus
define a helper function `withSizedVars`, that simply repeats `withSizedVar`
for each variable in its input.

> withSizedVars :: MonadReader ResolveEnv m => VarSize -> [String] -> m a -> m a
> withSizedVars vs xs m = foldr (withSizedVar vs) m xs

Of course, we also define the "easy" version of the above, where all the variables
are set to `Unknown`.

> withVars :: MonadReader ResolveEnv m => [String] -> m a -> m a
> withVars xs m = foldr withVar m xs

Next up, we define a way to set the `reCurrentDef` field to a definition. Such functions
take a lot of arguments: the `cdFutureTerm` that represents a handle on
the resulting definition, the `cdType` that represents (unsurprisingly) the definition's type,
and some definition-specific parameters. For instance, the `withFun` function also accepts
a list of the function's parameters and the raw version of the function that we received from
the parser.

> withFun :: MonadReader ResolveEnv m => S.Term -> S.Term -> [S.Term] -> ParseFun -> m a -> m a
> withFun t tt ps f = local $ \re -> re { reCurrentDef = Just (CurrentDef t tt $ Right $ CurrentFun ps f) }

If we're entering the body of a function, there are a few other things we might want to do other
than just set the `reCurrentDef` field. Since we're likely about to resolve the function's body,
we also want to introduce the function's parameters (all tagged `Original`, since they
are the inputs to our function), as well as the function itself (tagged `Self` to indicate
recursion). We combine all of these operations into `withFunction`.

> withFunction :: MonadReader ResolveEnv m => S.Term -> S.Term -> [S.Term] -> ParseFun -> m a -> m a
> withFunction t tt ps f = withFun t tt ps f . withSizedVar Self (pfName f) . withSizedVars Original (pfParamNames f)

Similarly, the `withInd` function accepts, in addition to the term and its type, the list
of the inductive definition's parameters, index types, and the raw version of the inductive
definition received from the parser.

> withInd :: MonadReader ResolveEnv m => S.Term -> S.Term -> [S.Term] -> [S.Term] -> ParseInd -> m a -> m a
> withInd t tt ps is i = local $ \re -> re { reCurrentDef = Just (CurrentDef t tt $ Left $ CurrentInd ps is i) }

Just as with `withFunction`, we define a `withInductive` function that not only sets the current
definition to an inductive data type, but also introduces its parametersm along with a reference
to the data type itself, into the environment. This time we don't bother tagging the parameters
as `Original`, since we need not detect recursion for data types.

> withInductive :: MonadReader ResolveEnv m => S.Term -> S.Term -> [S.Term] -> [S.Term] -> ParseInd -> m a -> m a
> withInductive t tt ps is pi = withInd t tt ps is pi . withSizedVar Self (piName pi) . withVars (piParamNames pi)

We're almost done with environment modifiers! The last couple of modifiers deal with the
`reApps` field of our environment. The first is called `withApp`, which lets us know
that we have descended into the right hand side of an application, and thus the current
term we're considering is applied to one more argument.

> withApp :: MonadReader ResolveEnv m => ParseTerm -> m a -> m a
> withApp pt = local $ \re -> re { reApps = pt : reApps re }

If we descend into something like a lambda abstraction, whatever terms were
applied to the current term are no longer meaningful (it's more complicated
to track the sizes of variable across aliasing). To be safe rather than sorry,
we discard all applications so far when processing such terms. This is strictly
a conservative strategy, sicne it will never cause false positive decreasing
arguments, but may
{{< sidenote "right" "fixpoint-note" "fail to detect valid instances of recursion." >}}
Indeed, even "real" languages like Coq have this problem. Some "elegant" ways of
defining functions are ruled out by the termination checker. Some  languages (Coq included)
allow you to manually prove termination, by specifying a "measure" on one or more of your arguments,
and proving that it decreases with every function call. We will not do so, however, since such
features are rather complicated.
{{< /sidenote >}}

> clearApps :: MonadReader ResolveEnv m => m a -> m a
> clearApps = local $ \re -> re { reApps = [] }

With modification out of the way, we're left with retrieval. Our first
function of this kind is `currentModule`, which retrieves the current module's
name, in the form of a `Symbol`.

> currentModule :: MonadReader ResolveEnv m => m Symbol
> currentModule = asks (mhName . reHeader)
>
>
> lookupVar :: MonadReader ResolveEnv m => String -> m (Maybe (Either () Int))
> lookupVar s = asks (getFirst . (findSelf <> findRef) . reVars)
>     where
>         findRef = First . fmap Right . elemIndex s . map fst
>         findSelf = First . (>>= intoSelf) . lookup s
>         intoSelf Self = Just (Left ())
>         intoSelf _ = Nothing
>
> varSize :: MonadReader ResolveEnv m => String -> m VarSize
> varSize s = asks (fromMaybe Unknown . lookup s . reVars)
>
> data ResolveState = ResolveState
>     { rsScope :: GlobalScope
>     , rsDefs :: Map.Map String Definition
>     , rsDecreasing :: Maybe (Set.Set String)
>     }
>
> class (MonadReader ResolveEnv m, MonadState ResolveState m, MonadError ResolveError m, MonadFix m)
>     => MonadResolver m where
>
> instance (MonadReader ResolveEnv m, MonadState ResolveState m, MonadError ResolveError m, MonadFix m)
>     => MonadResolver m where
>
> instantiate :: MonadInfer k m => Maybe k -> ResolveTerm -> m (S.ParamTerm k)
> instantiate mt = traverse inst
>     where
>         self = maybe mzero return mt
>         inst SelfRef = self
>         inst Placeholder = fresh
>
> strip :: MonadInfer k m => Int -> S.ParamTerm k -> m S.Term
> strip i t = reifyTermOffset i t >>= traverse (const (throwError undefined))
>
> subst :: Eq k => k -> S.Term -> S.ParamTerm k -> S.ParamTerm k
> subst k t = subst'
>     where
>         subst' (S.Param k') | k == k' = parameterize t
>         subst' (S.Abs l r) = S.Abs (subst' l) (subst' r)
>         subst' (S.App l r) = S.App (subst' l) (subst' r)
>         subst' (S.Let l r) = S.Let (subst' l) (subst' r)
>         subst' (S.Prod l r) = S.Prod (subst' l) (subst' r)
>         subst' (S.Case t i tt ts) = S.Case (subst' t) i (subst' tt) (map subst' ts)
>         subst' t = t
> 
> mkSelf :: MonadInfer k m => S.Term -> m k
> mkSelf t = do
>     k <- fresh
>     bind k (Context [] (Just $ parameterize t) Nothing)
>     return k
>
> mkMSelf :: MonadInfer k m => Maybe S.Term -> m (Maybe k) 
> mkMSelf = traverse mkSelf
>
> selfType :: MonadResolver m => m (Maybe S.Term)
> selfType = asks (fmap cdType . reCurrentDef)
>
> selfInductive :: MonadResolver m => m (CurrentDef, CurrentInd)
> selfInductive = do
>     mcd <- asks reCurrentDef
>     case mcd of
>         Just cd@CurrentDef{cdExtra=Left ci} -> return (cd, ci)
>         _ -> throwError InvalidResolve
>
> selfFunction :: MonadResolver m => m (CurrentDef, CurrentFun)
> selfFunction = do
>     mcd <- asks reCurrentDef
>     case mcd of
>         Just cd@CurrentDef{cdExtra=Right cf} -> return (cd, cf)
>         _ -> throwError InvalidResolve
>
> elaborateInEnv :: MonadResolver m => Maybe (S.Term, S.Term) -> [ResolveTerm] -> ResolveTerm -> m ([S.Term], S.Term)
> elaborateInEnv mtd env t = inferWithin $ do
>     let mtt = snd <$> mtd
>     let mt = fst <$> mtd
>     self <- mkMSelf mtt
>     ienv <- mapM (instantiate self) env
>     it <- instantiate self t
>     infer $ foldr S.Abs it ienv
>     let stripBody = strip (length env) 
>     let stripEnv = zipWithM strip [0..]
>     case (mt, self) of
>         (Just t', Just k) -> liftA2 (,) (stripEnv $ map (subst k t') ienv) (stripBody $ subst k t' it)
>         _ -> liftA2 (,) (stripEnv ienv) (stripBody it)
>
> elaboratePlain :: MonadResolver m => ResolveTerm -> m S.Term
> elaboratePlain t = snd <$> elaborateInEnv Nothing [] t
>
> elaborateInd :: MonadResolver m => [ResolveTerm] -> m [S.Term]
> elaborateInd pis = fst <$> elaborateInEnv Nothing pis (S.Sort Prop)
>
> elaborateFun :: MonadResolver m => ResolveTerm -> m S.Term
> elaborateFun bt = do
>     (cd, cf) <- selfFunction
>     (_, ebt) <- elaborateInEnv (Just (cdFutureTerm cd, cdType cd)) (parameterizeAll $ cfParams cf) bt
>     return ebt
>
> elaborateCon :: MonadResolver m => [ResolveTerm] -> [ResolveTerm] -> m ([S.Term], [S.Term])
> elaborateCon ps is = do
>     (cd, ci) <- selfInductive
>     let ips = ciParams ci
>     let allPs = parameterizeAll ips ++ ps
>     let paramRefs = map (S.Ref . (+ length ps)) $ reverse [0..length ips -1]
>     let ret = foldl S.App (S.Param SelfRef) (paramRefs ++ is)
>     (eps, eret) <- elaborateInEnv (Just (cdFutureTerm cd, cdType cd)) allPs ret
>     (_, eretas) <- liftEither $ first (const InvalidResolve) $ collectApps eret
>     return (drop (length ips) eps, drop (length ips) eretas)
>
> inferWithin :: MonadResolver m => InferU String a -> m a
> inferWithin m = liftEither $ first InferError $ runInferU m 
>
> withNoDecreasing :: MonadState ResolveState m => m a -> m a
> withNoDecreasing m = do
>     dec <- gets rsDecreasing
>     modify $ \rs -> rs { rsDecreasing = Nothing }
>     a <- m
>     modify $ \rs -> rs { rsDecreasing = dec }
>     return a
>
> emitDecreasing :: MonadState ResolveState m => Set.Set String -> m ()
> emitDecreasing s = modify $ \rs -> rs { rsDecreasing = updateDec (rsDecreasing rs) }
>     where
>         updateDec Nothing = Just s
>         updateDec (Just s') = Just $ Set.intersection s s'
> 
> emitExport :: MonadResolver m => String -> ExportVariant -> m ()
> emitExport s ev = do
>     mn <- currentModule
>     let export = Export ev mn
>     let nQual = Map.singleton (qualName mn s) export
>     let nUnqual = Map.singleton (unqualName s) [export]
>     let ngs = GlobalScope nQual nUnqual
>     gs' <- gets ((`mergeScopes` ngs) . rsScope) >>= (liftEither . first ImportError)
>     modify $ \rs -> rs { rsScope = gs' }
>
> emitInd :: MonadResolver m => String -> Inductive -> m ()
> emitInd s i = emitExport s (IndExport i)
>
> emitFun :: MonadResolver m => String -> Function -> m ()
> emitFun s f = emitExport s (FunExport f)
>
> emitDef :: MonadResolver m => String -> Definition -> m ()
> emitDef s d = modify $ \rs -> rs { rsDefs = Map.insert s d $ rsDefs rs }
>
> emitConstructors :: MonadResolver m => Inductive -> m ()
> emitConstructors i = zipWithM_ emitConstructor [0..] (iConstructors i)
>     where emitConstructor ci c = emitExport (cName c) (ConExport i ci)
>
> insertLeading :: [ParamType] -> ResolveTerm -> ResolveTerm
> insertLeading ps t = foldl S.App t $ replicate (length $ takeWhile (==Inferred) ps) (S.Param Placeholder)
>
> exportToTerm :: Export -> ResolveTerm
> exportToTerm e = case eVariant e of
>     FunExport f -> insertLeading (map snd $ fArity f) (S.Fun f)
>     ConExport i ci -> S.Constr i ci
>     IndExport i -> S.Ind i
> 
> narrowExports :: MonadResolver m => [Export] -> m Export
> narrowExports [] = throwError UnknownReference
> narrowExports [x] = return x
> narrowExports _ = throwError AmbiguousReference
>
> smallerParams :: [Maybe (String, VarSize)] -> Set.Set String
> smallerParams mps = Set.fromList $ catMaybes $ map (>>=(varParent . snd)) mps
>
> recordFixpoint :: MonadResolver m => m ()
> recordFixpoint =
>     do
>         asks reCurrentDef
>             >>= maybe (throwError InvalidFixpoint) return
>             >>= either (const $ return ()) (record . cfParsed) . cdExtra
>     where
>         record cf = do
>             params <- take (length $ pfArity cf) <$> asks reApps
>             smallerParams <- smallerParams <$> mapM termSize params
>             emitDecreasing smallerParams
> 
> lookupUnqual :: MonadResolver m => String -> m ResolveTerm
> lookupUnqual s = do
>     es <- gets (fromMaybe [] . Map.lookup (unqualName s) . sUnqualified . rsScope)
>     exportToTerm <$> narrowExports es
>
> lookupQual :: MonadResolver m => Symbol -> m ResolveTerm
> lookupQual s = do
>     me <- gets (Map.lookup s . sQualified . rsScope)
>     maybe (throwError UnknownReference) (return . exportToTerm) me
>
> lookupRef :: MonadResolver m => ParseRef -> m ResolveTerm
> lookupRef (SymRef s) = lookupQual s
> lookupRef (StrRef s) = lookupUnqual s
>
> lookupInd :: MonadResolver m => ParseRef -> m S.Inductive
> lookupInd r = do
>     t <- lookupRef r
>     case t of
>         S.Ind i -> return i
>         _ -> throwError NotInductive
>
> resolveIndRef :: MonadResolver m => ParseIndRef -> m (S.Inductive, [String])
> resolveIndRef (r, is) = do
>     i <- lookupInd r
>     if length (iArity i) == length is
>      then return (i, is)
>      else throwError InvalidArity
>
> resolveBranch :: MonadResolver m => VarSize -> ParseBranch -> m (String, ResolveTerm)
> resolveBranch vs (s, ps, t) = (,) s <$> withSizedVars vs ps (resolveTerm t)
>
> matchBranch :: MonadResolver m => [(String, ResolveTerm)] -> Constructor -> m ResolveTerm
> matchBranch bs c = maybe (throwError IncompleteMatch) return $ lookup (cName c) bs 
>
> termSize :: MonadResolver m => ParseTerm -> m (Maybe (String, VarSize))
> termSize (Ref (StrRef s)) = Just . (,) s <$> varSize s
> termSize _ = return Nothing
>
> caseTermSize :: MonadResolver m => ParseTerm -> m VarSize
> caseTermSize t = do
>     mts <- termSize t
>     return $ case mts of
>         Just (s, Original) -> SmallerThan s
>         Just (_, vs) -> vs
>         _ -> Unknown
>
> currentParamTypes :: MonadResolver m => m (Maybe [ParamType])
> currentParamTypes = do
>     mcd <- asks reCurrentDef
>     return $ case cdExtra <$> mcd of
>         Just (Right cf) -> Just $ pfParamTypes $ cfParsed cf
>         Just Left{} -> Nothing
>
> resolveTerm :: MonadResolver m => ParseTerm -> m ResolveTerm
> resolveTerm (Ref (StrRef s)) = do
>     vref <- lookupVar s
>     case vref of
>         Just Left{} -> do
>             recordFixpoint
>             pts <- currentParamTypes
>             return $ insertLeading (fromMaybe [] pts) (S.Param SelfRef)
>         Just (Right i) -> return $ (S.Ref i)
>         Nothing -> lookupUnqual s
> resolveTerm (Ref (SymRef s)) = lookupQual s
> resolveTerm (Abs (x, tt) t) = clearApps $ liftA2 S.Abs (resolveTerm tt) (withVar x $ resolveTerm t)
> resolveTerm (App l r) = liftA2 S.App (withApp r $ resolveTerm l) (resolveTerm r)
> resolveTerm (Let (x, t) ti) = liftA2 S.Let (clearApps $ resolveTerm t) (withVar x $ resolveTerm ti)
> resolveTerm (Prod (x, tt) t) = clearApps $ liftA2 S.Prod (resolveTerm tt) (withVar x $ resolveTerm t)
> resolveTerm (Sort s) = return $ S.Sort s
> resolveTerm e@(Case t x ir tt bs) = do
>     t' <- clearApps $ resolveTerm t
>     vs <- caseTermSize t
>     (i, is) <- resolveIndRef ir
>     tt' <- clearApps $ withVars (x:is) $ resolveTerm tt
>     bs' <- mapM (resolveBranch vs) bs
>     cbs <- mapM (matchBranch bs') $ iConstructors i
>     return $ S.Case t' i tt' cbs
>
> decreasingIndices :: [String] -> [String] -> [Int]
> decreasingIndices args dec = sort $ catMaybes $ map (`elemIndex` args) dec
>
> findDecreasing :: MonadResolver m => [String] -> m (Maybe Int)
> findDecreasing args = do
>     dec <- fmap (decreasingIndices args . Set.toList) <$> gets rsDecreasing
>     case dec of
>         Just (x:_) -> return $ Just x
>         Just [] -> throwError InvalidFixpoint
>         _ -> return Nothing
>
> resolveFun :: MonadResolver m => ParseFun -> m Function
> resolveFun f = do
>     fts <- resolveTerm (pfType f) >>= elaboratePlain
>     (ats, rt) <- liftEither $ collectFunArgs (pfParamNames f) fts
>     rec f' <- withNoDecreasing $ withFunction (S.Fun f') fts ats f $ do
>          fb <- resolveTerm (pfBody f) >>= elaborateFun
>          dec <- findDecreasing (pfParamNames f)
>          return $ Function (pfName f) (zip ats (pfParamTypes f)) rt fb dec
>     emitFun (pfName f) f'
>     return f'
>
> collectFunArgs :: [String] -> (S.ParamTerm a) -> Either ResolveError ([S.ParamTerm a], S.ParamTerm a)
> collectFunArgs [] t = return $ ([], t)
> collectFunArgs (_:xs) (S.Prod l r) = first (l:) <$> collectFunArgs xs r
> collectFunArgs _ _ = throwError InvalidArity
>
> resolveParams :: MonadResolver m => [ParseParam] -> m [ResolveTerm]
> resolveParams = foldr (\(x, t) m -> liftA2 (:) (resolveTerm t) (withVar x m)) (return [])
>
> resolveConstr :: MonadResolver m => ParseConstr -> m S.Constructor
> resolveConstr pc = do
>     ps' <- resolveParams (pcAllParams pc)
>     is' <- withVars (pcParamNames pc) $ mapM resolveTerm (pcIndices pc)
>     (ps'', is'') <- elaborateCon ps' is'
>     return $ Constructor (zip ps'' (pcParamTypes pc)) is'' (pcName pc)
>
> resolveInd :: MonadResolver m => ParseInd -> m S.Inductive
> resolveInd pi = do
>     its <- resolveParams (piAllParams pi ++ piArity pi) >>= elaborateInd
>     let it = foldr S.Prod (S.Sort $ piSort pi) its
>     let (ps', is') = splitAt (length $ piParams pi) its
>     rec i' <- withInductive (S.Ind i') it ps' is' pi $ do
>          cs <- mapM resolveConstr (piConstructors pi)
>          return $ Inductive (zip ps' (piParamTypes pi)) is' (piSort pi) cs (piName pi)
>     emitInd (piName pi) i' 
>     emitConstructors i'
>     return i'
> 
> resolveDef :: MonadResolver m => ParseDef -> m Definition
> resolveDef d = do
>     dc <- either (fmap IndDef . resolveInd) (fmap FunDef . resolveFun) d
>     let def = Definition Public dc
>     emitDef (dName def) def
>     return def
>
> resolveDefs :: ModuleHeader -> GlobalScope -> [(String, ParseDef)] -> Either ResolveError (Map.Map String Definition)
> resolveDefs mh gs ps = (rsDefs . snd) <$> (runExcept $ runReaderT (runStateT (mapM (resolveDef . snd) ps) state) env)
>     where
>         env = ResolveEnv { reVars = [], reHeader = mh, reCurrentDef = Nothing, reApps = [] }
>         state = ResolveState { rsScope = gs, rsDefs = Map.empty, rsDecreasing = Nothing }
