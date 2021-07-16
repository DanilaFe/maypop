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
>     deriving Show
>
> data VarSize = Self | Original | SmallerThan String | Unknown deriving Show
>
> data ResolveParam = SelfRef | Placeholder
>
> type ResolveTerm = S.ParamTerm ResolveParam
>
> varParent :: VarSize -> Maybe String
> varParent (SmallerThan s) = Just s
> varParent _ = Nothing
>
> data ResolveEnv = ResolveEnv
>     { reVars :: [(String, VarSize)]
>     , reHeader :: ModuleHeader
>     , reCurrentDef :: Maybe (Either ParseInd ParseFun)
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
> withFun :: MonadReader ResolveEnv m => ParseFun -> m a -> m a
> withFun f = local $ \re -> re { reCurrentDef = Just (Right f) }
>
> withInd :: MonadReader ResolveEnv m => ParseInd -> m a -> m a
> withInd f = local $ \re -> re { reCurrentDef = Just (Left f) }
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
> strip t = reifyTerm t >>= traverse (const (throwError undefined))
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
> elaborateInEnv :: MonadResolver m => Maybe S.Term -> [ResolveTerm] -> ResolveTerm -> m ([S.Term], S.Term)
> elaborateInEnv mt env t = inferWithin $ do
>     self <- mkMSelf mt
>     ienv <- mapM (instantiate self) env
>     it <- instantiate self t
>     infer $ foldl (flip S.Abs) it ienv
>     liftA2 (,) (mapM strip ienv) (strip it)
>
> elaborateInd :: MonadResolver m => [ResolveTerm] -> Sort -> m [S.Term]
> elaborateInd env s = fst <$> elaborateInEnv Nothing env (S.Sort s)
>
> elaborateConstr :: MonadResolver m => S.Term -> [ResolveTerm] -> [ResolveTerm] -> m ([S.Term], [S.Term])
> elaborateConstr t env is = inferWithin $ do
>     self <- mkSelf t
>     ienv <- mapM (instantiate $ Just self) env
>     iis <- mapM (instantiate $ Just self) is
>     let test = foldr S.Abs (foldl S.App (S.Param self) iis) ienv
>     infer $ test
>     liftA2 (,) (mapM strip ienv) (mapM strip iis)
>
> elaborate :: MonadResolver m => Maybe S.Term -> ResolveTerm -> m S.Term
> elaborate mt t = snd <$> elaborateInEnv mt [] t
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
> exportToTerm :: Export -> S.ParamTerm a
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
>             >>= either (const $ return ()) record
>     where
>         record cf = do
>             params <- take (length $ pfArity cf) <$> asks reApps
>             smallerParams <- smallerParams <$> mapM termSize params
>             emitDecreasing smallerParams
> 
> lookupUnqual :: MonadResolver m => String -> m (S.ParamTerm a)
> lookupUnqual s = do
>     es <- gets (fromMaybe [] . Map.lookup (unqualName s) . sUnqualified . rsScope)
>     exportToTerm <$> narrowExports es
>
> lookupQual :: MonadResolver m => Symbol -> m (S.ParamTerm a)
> lookupQual s = do
>     me <- gets (Map.lookup s . sQualified . rsScope)
>     maybe (throwError UnknownReference) (return . exportToTerm) me
>
> lookupRef :: MonadResolver m => ParseRef -> m (S.ParamTerm a)
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
>     fts <- resolveTerm (pfType f) >>= elaborate Nothing
>     (ats, rt) <- liftEither $ collectFunArgs (pfArity f) fts
>     f' <- withNoDecreasing $ withFun f $ withSizedVar Self (pfName f) $ withSizedVars Original (pfArity f) $ do
>          (_, fb) <- resolveTerm (pfBody f) >>= elaborateInEnv (Just fts) (map parameterize ats)
>          dec <- findDecreasing (pfArity f)
>          return $ Function (pfName f) ats rt fb dec
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
> resolveConstr :: MonadResolver m => S.Term -> [S.Term] -> ParseConstr -> m S.Constructor
> resolveConstr it ips pc = do
>     ps' <- (parameterizeAll ips++) <$> resolveParams (pcParams pc)
>     is' <- withVars (fst $ unzip $ pcParams pc) $ mapM resolveTerm (pcIndices pc)
>     (ps'', is'') <- elaborateConstr it ps' is'
>     return $ Constructor ps'' is'' (pcName pc)
>
> resolveInd :: MonadResolver m => ParseInd -> m S.Inductive
> resolveInd pi = do
>     its <- resolveParams (piParams pi ++ piArity pi) >>= (`elaborateInd` piSort pi)
>     let it = foldr S.Prod (S.Sort $ piSort pi) its
>     let (ps', is') = splitAt (length $ piParams pi) its
>     i' <- withInd pi $ withSizedVar Self (piName pi) $ withVars (map fst $ piParams pi) $ do
>          cs <- mapM (resolveConstr it ps') (piConstructors pi)
>          return $ Inductive ps' is' (piSort pi) cs (piName pi)
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
