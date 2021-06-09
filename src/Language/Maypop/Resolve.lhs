In this module, we will convert the data structures generated by our
parser (which may or may not be well-formed) into Maypop terms.

> {-# LANGUAGE RecursiveDo #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE MonoLocalBinds #-}
> module Language.Maypop.Resolve where
> import Language.Maypop.Syntax hiding (ParamTerm(..), Term)
> import qualified Language.Maypop.Syntax as S
> import Language.Maypop.Parser
> import Language.Maypop.Unification
> import Language.Maypop.Eval
> import Language.Maypop.Search hiding (instantiate)
> import Language.Maypop.Checking hiding (NotInductive)
> import Language.Maypop.Modules hiding (function)
> import Control.Applicative
> import Control.Monad.Reader
> import Control.Monad.Identity
> import Control.Monad.State
> import Control.Monad.Except
> import Control.Monad.Writer
> import qualified Data.Map as Map
> import qualified Data.Set as Set
> import Data.List
> import Data.Maybe
> import Data.Bifunctor
> import Debug.Trace
> import Data.Foldable
>
> data ResolveError
>     = UnknownReference
>     | AmbiguousReference
>     | NotInductive
>     | InvalidArity
>     | IncompleteMatch
>     | ImportError ImportError
>     | InvalidFixpoint
>     | ElaborateFailed TypeError
>     deriving Show
>
> data VarSize = SelfRef | Original | SmallerThan String | Unknown deriving Show
>
> data ResolveParam = Self | Placeholder deriving Show
>
> type ResolveTerm = S.ParamTerm ResolveParam
>
> instantiate
>     :: (MonadWriter [(k, S.ParamTerm k)] m,  MonadUnify k (Context k) m)
>     => ResolveTerm -> m (k, S.ParamTerm k)
> instantiate rt =
>     do
>         selfVar <- fresh
>         (,) selfVar <$> traverse (inst selfVar) rt
>     where
>         inst x Self = return x
>         inst x Placeholder = do
>             x <- fresh
>             y <- fresh
>             tell [(x, S.Param y)]
>             return x
>
> elaborate :: MonadResolver m => Maybe S.Term -> ResolveTerm -> m S.Term
> elaborate mt rt =
>     do
>         env <- parameterizeAll <$> asks reEnv
>         cd <- asks reCurrentDef
>         rs <- intoRecipies <$> gets rsScope
>         let e = runInferU (InferEnv env Map.empty) (elab rs cd)
>         liftEither $ first ElaborateFailed e
>     where
>         elab :: [Recipe Meta] -> Maybe (ParseDef, S.Term) -> InferU String S.Term
>         elab rs mcd = runUnifyT $ do
>             ((x, pt), ts) <- runWriterT $ instantiate rt
>             let xt = maybe [] (return . (,) x . parameterize . snd) mcd
>             local (setParams $ Map.fromList $ ts ++ xt) $ do
>                 infer pt
>                 pt' <- reifyTerm pt >>= fillAll rs >>=reifyTerm
>                 maybe (throwError TypeError) return
>                     $ strip $ maybe pt' (flip (subst x) pt')
>                     $ parameterize <$> mt
>
> replaceParams :: Monad m => (k -> m (S.ParamTerm k)) -> S.ParamTerm k -> m (S.ParamTerm k)
> replaceParams f = replace
>     where
>         replace (S.Param k) = f k
>         replace (S.Abs l r) = liftA2 S.Abs (replace l) (replace r)
>         replace (S.App l r) = liftA2 S.App (replace l) (replace r)
>         replace (S.Let l r) = liftA2 S.Let (replace l) (replace r)
>         replace (S.Prod l r) = liftA2 S.Prod (replace l) (replace r)
>         replace (S.Case t i tt ts) = liftA3 (`S.Case` i) (replace t) (replace tt) (mapM replace ts)
>         replace t = return t
>
> fillAll :: (Show k, MonadInfer k m, MonadUnify k (Context k) m) => [Recipe Meta] -> S.ParamTerm k -> m (S.ParamTerm k)
> fillAll = replaceParams . fill
>
> fill :: (Show k, MonadInfer k m, MonadUnify k (Context k) m) => [Recipe Meta] -> k -> m (S.ParamTerm k)
> fill rs k = do
>     mh <- bound k
>     case mh of
>         Just (Context{ctxEnv=env, ctxTerm=Nothing}) -> do
>             let t = S.Param k
>             tt <- eval <$> (infer t >>= reifyTerm)
>             ttt <- eval <$> (infer tt >>= reifyTerm)
>             env' <- asks ieRefs
>             case (strip tt, ttt) of
>                 (Just tt', S.Sort Constraint)
>                     | [x] <- findIndices ((==eval tt) . eval) env' -> bind k (Context (map Valid env') (Just $ S.Ref x)) >> return t
>                     | Right rt <- runSearch rs tt' -> return (parameterize rt)
>                 _ -> return t
>         Nothing -> return (S.Param k)
> 
> subst :: Eq k => k -> S.ParamTerm k -> S.ParamTerm k -> S.ParamTerm k
> subst k rt = runIdentity . replaceParams subst'
>     where
>         subst' k'
>             | k == k' = return rt
>             | otherwise = return (S.Param k')
>
> leadingInferred :: [(ParamType, a)] -> Int
> leadingInferred = length . takeWhile ((==Inferred) . fst)
>
> varParent :: VarSize -> Maybe String
> varParent (SmallerThan s) = Just s
> varParent _ = Nothing
>
> data ResolveEnv = ResolveEnv
>     { reVars :: [(String, VarSize)]
>     , reHeader :: ModuleHeader
>     , reCurrentDef :: Maybe (ParseDef, S.Term)
>     , reApps :: [ParseTerm]
>     , reEnv :: [S.Term]
>     }
>
> withSizedVar :: MonadReader ResolveEnv m => VarSize -> String -> m a -> m a
> withSizedVar vs s = local (\re -> re { reVars = (s,vs) : reVars re })
>
> withVar :: MonadReader ResolveEnv m => String -> m a -> m a
> withVar = withSizedVar Unknown
>
> withSizedVars :: MonadReader ResolveEnv m => VarSize -> [String] -> m a -> m a
> withSizedVars vs xs m = foldr (withSizedVar vs) m xs
>
> withVars :: MonadReader ResolveEnv m => [String] -> m a -> m a
> withVars xs m = foldr withVar m xs
>
> withFun :: MonadReader ResolveEnv m => ParseFun -> S.Term -> m a -> m a
> withFun f t = local $ \re -> re { reCurrentDef = Just (Right f, t) }
>
> withInd :: MonadReader ResolveEnv m => ParseInd -> S.Term -> m a -> m a
> withInd i t = local $ \re -> re { reCurrentDef = Just (Left i, t) }
>
> withApp :: MonadReader ResolveEnv m => ParseTerm -> m a -> m a
> withApp pt = local $ \re -> re { reApps = pt : reApps re }
>
> withRef :: MonadReader ResolveEnv m => S.Term -> m a -> m a
> withRef t = local $ \re -> re { reEnv = map (offsetFree 1) $ t : reEnv re }
>
> withRefs :: MonadReader ResolveEnv m => [S.Term] -> m a -> m a
> withRefs ts m = foldr withRef m ts
>
> clearApps :: MonadReader ResolveEnv m => m a -> m a
> clearApps = local $ \re -> re { reApps = [] }
>
> currentModule :: MonadReader ResolveEnv m => m Symbol
> currentModule = asks (mhName . reHeader)
>
> lookupVar :: MonadReader ResolveEnv m => String -> m (Maybe (Either () Int))
> lookupVar s = asks (getFirst . (findSelf <> findRef) . reVars)
>     where
>         findRef = First . fmap Right . elemIndex s . map fst
>         findSelf = First . (>>= intoSelf) . lookup s
>         intoSelf SelfRef = Just (Left ())
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
> exportToTerm :: Export -> ResolveTerm
> exportToTerm e = case eVariant e of
>     FunExport f -> foldl S.App (S.Fun f) $ replicate (leadingInferred $ fArity f) (S.Param Placeholder)
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
>             >>= either (const $ return ()) record . fst
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
> matchBranch :: MonadResolver m => [(String, S.ParamTerm a)] -> Constructor -> m (S.ParamTerm a)
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
>         Just (s, SelfRef) -> Unknown
>         Just (_, vs) -> vs
>         _ -> Unknown
>
> resolveTerm :: MonadResolver m => ParseTerm -> m ResolveTerm
> resolveTerm (Ref (StrRef s)) = do
>     vref <- lookupVar s
>     case vref of
>         Just Left{} -> recordFixpoint >> return (S.Param Self)
>         Just (Right i) -> return (S.Ref i)
>         Nothing -> lookupUnqual s
> resolveTerm (Ref (SymRef s)) = lookupQual s
> resolveTerm (Abs (x, tt) t) = clearApps $ liftA2 S.Abs (resolveTerm tt) (withVar x $ resolveTerm t)
> resolveTerm (App l r) = liftA2 S.App (withApp r $ resolveTerm l) (resolveTerm r)
> resolveTerm (Let (x, t) ti) = liftA2 S.Let (clearApps $ resolveTerm t) (withVar x $ resolveTerm ti)
> resolveTerm (Prod (x, tt) t) = clearApps $ liftA2 S.Prod (resolveTerm tt) (withVar x $ resolveTerm t)
> resolveTerm (Sort s) = return $ S.Sort s
> resolveTerm (Case t x ir tt bs) = do
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
>         _ -> return $ Nothing
>
> allExplicit :: [S.ParamTerm a] -> [(ParamType, S.ParamTerm a)]
> allExplicit = map ((,) Explicit)
>
> resolveFun :: MonadResolver m => ParseFun -> m S.Function
> resolveFun f = do
>     fts <- resolveTerm (pfType f) >>= elaborate Nothing
>     (ats, rt) <- liftEither $ collectFunArgs (pfArity f) fts
>     rec f' <- withNoDecreasing $ withRefs (map snd ats) $ withSizedVar SelfRef (pfName f) $ withFun f fts $  do
>          fb <- withSizedVars Original (pfArgNames f) (resolveTerm (pfBody f)) >>= elaborate (Just (S.Fun f'))
>          md <- findDecreasing (pfArgNames f) 
>          return $ Function (pfName f) ats rt fb md
>     emitFun (pfName f) f' 
>     return f'
>
> collectFunArgs :: [(ParamType, String)] -> S.ParamTerm a -> Either ResolveError ([(ParamType, S.ParamTerm a)], S.ParamTerm a)
> collectFunArgs [] t = return $ ([], t)
> collectFunArgs ((pt,_):xs) (S.Prod l r) = first ((pt,l):) <$> collectFunArgs xs r
> collectFunArgs _ _ = throwError InvalidArity
>
> resolveParams :: MonadResolver m => Maybe S.Term -> [ParseParam] -> m [S.Term]
> resolveParams _ [] = return []
> resolveParams mt ((x,t):xs) = do
>     t' <- resolveTerm t >>= elaborate mt
>     ts <- withVar x $ withRef t' $ resolveParams mt xs
>     return (t':ts)
>
> resolveConstr :: MonadResolver m => S.Inductive -> ParseConstr -> m S.Constructor
> resolveConstr i pc = do
>     let mt = Just (S.Ind i)
>     ps' <- resolveParams mt (pcParams pc)
>     is' <- withVars (fst $ unzip $ pcParams pc) $ mapM ((>>=elaborate mt) . resolveTerm) (pcIndices pc)
>     return $ Constructor (allExplicit ps') is' (pcName pc)
>
> resolveInd :: MonadResolver m => ParseInd -> m S.Inductive
> resolveInd pi = do
>     ips <- resolveParams Nothing (piParams pi ++ piArity pi)
>     let (ps', is') = splitAt (length $ piParams pi) ips
>     let it = foldr S.Prod (S.Sort $ piSort pi) ips
>     rec i' <- withRefs ps' $ withSizedVar SelfRef (piName pi) $ withInd pi it $ do
>          cs <- withVars (map fst $ piParams pi) $ mapM (resolveConstr i') (piConstructors pi)
>          return $ Inductive (allExplicit ps') is' (piSort pi) cs (piName pi)
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
>         env = ResolveEnv { reVars = [], reHeader = mh, reCurrentDef = Nothing, reApps = [], reEnv = [] }
>         state = ResolveState { rsScope = gs, rsDefs = Map.empty, rsDecreasing = Nothing }
