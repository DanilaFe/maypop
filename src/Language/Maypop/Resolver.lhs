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
> import Debug.Trace
>
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
>
> data VarSize = Self | Original | SmallerThan String | Unknown deriving Show
>
> data ResolveParam = SelfRef | Placeholder deriving (Eq, Show)
>
> type ResolveTerm = S.ParamTerm ResolveParam
>
> varParent :: VarSize -> Maybe String
> varParent (SmallerThan s) = Just s
> varParent _ = Nothing
>
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
>
> data CurrentDef = CurrentDef
>     { cdFutureTerm :: S.Term
>     , cdType :: S.Term
>     , cdExtra :: Either CurrentInd CurrentFun
>     }
>
> data ResolveEnv = ResolveEnv
>     { reVars :: [(String, VarSize)]
>     , reHeader :: ModuleHeader
>     , reCurrentDef :: Maybe CurrentDef
>     , reApps :: [ParseTerm]
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
> withFun :: MonadReader ResolveEnv m => S.Term -> S.Term -> [S.Term] -> ParseFun -> m a -> m a
> withFun t tt ps f = local $ \re -> re { reCurrentDef = Just (CurrentDef t tt $ Right $ CurrentFun ps f) }
>
> withFunction :: MonadReader ResolveEnv m => S.Term -> S.Term -> [S.Term] -> ParseFun -> m a -> m a
> withFunction t tt ps f = withFun t tt ps f . withSizedVar Self (pfName f) . withSizedVars Original (pfParamNames f)
>
> withInd :: MonadReader ResolveEnv m => S.Term -> S.Term -> [S.Term] -> [S.Term] -> ParseInd -> m a -> m a
> withInd t tt ps is i = local $ \re -> re { reCurrentDef = Just (CurrentDef t tt $ Left $ CurrentInd ps is i) }
>
> withInductive :: MonadReader ResolveEnv m => S.Term -> S.Term -> [S.Term] -> [S.Term] -> ParseInd -> m a -> m a
> withInductive t tt ps is pi = withInd t tt ps is pi . withSizedVar Self (piName pi) . withVars (piParamNames pi)
>
> withApp :: MonadReader ResolveEnv m => ParseTerm -> m a -> m a
> withApp pt = local $ \re -> re { reApps = pt : reApps re }
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
> strip :: MonadInfer k m => S.ParamTerm k -> m S.Term
> strip = traverse (const (throwError undefined))
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
>     case (mt, self) of
>         (Just t', Just k) -> liftA2 (,) (mapM (strip . subst k t') ienv) (strip $ subst k t' it)
>         _ -> liftA2 (,) (mapM strip ienv) (strip it)
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
>     FunExport f -> S.Fun f
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
> resolveTerm :: MonadResolver m => ParseTerm -> m ResolveTerm
> resolveTerm (Ref (StrRef s)) = do
>     vref <- lookupVar s
>     case vref of
>         Just Left{} -> recordFixpoint >> return (S.Param SelfRef)
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
