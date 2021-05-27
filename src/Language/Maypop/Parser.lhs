In this module, we'll write a Parsec-based parser for the Maypop language.
No explanations for now, this is long, subject to change, and kind of
repetitive.

> {-# LANGUAGE TupleSections #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE UndecidableInstances #-}
> {-# LANGUAGE MonoLocalBinds #-}
> {-# LANGUAGE RecursiveDo #-}
> module Language.Maypop.Parser where
> import Prelude hiding (pi)
> import Language.Maypop.Syntax hiding (ParamTerm(..), Term)
> import qualified Language.Maypop.Syntax as S
> import Language.Maypop.Modules
> import Language.Maypop.Unification
> import Language.Maypop.Checking hiding (NotInductive)
> import Control.Applicative hiding ((<|>), many)
> import Control.Monad.Reader
> import Control.Monad.State
> import Control.Monad.Except
> import Control.Monad.Writer
> import Text.Parsec
> import Text.Parsec.Token
> import Text.Parsec.Expr
> import qualified Data.Map as Map
> import qualified Data.Set as Set
> import Data.Char
> import Data.Bifunctor
> import Data.List
> import Data.Maybe
> import Data.Functor.Identity
>
> data ParseRef = SymRef Symbol | StrRef String deriving Show
>
> type ParseParam = (String, ParseTerm)
>
> data ParseTerm
>     = Ref ParseRef
>     | Abs ParseParam ParseTerm
>     | App ParseTerm ParseTerm
>     | Let ParseParam ParseTerm
>     | Prod ParseParam ParseTerm
>     | Sort Sort
>     | Case ParseTerm String ParseIndRef ParseTerm [ParseBranch]
>     deriving Show
>
> data ParseConstr = ParseConstr
>     { pcName :: String
>     , pcParams :: [ParseParam]
>     , pcIndices :: [ParseTerm]
>     }
>     deriving Show
>
> data ParseInd = ParseInd
>     { piName :: String
>     , piParams :: [ParseParam] 
>     , piArity :: [ParseParam]
>     , piSort :: Sort
>     , piConstructors :: [ParseConstr]
>     }
>     deriving Show
>
> data ParseFun = ParseFun
>     { pfName :: String
>     , pfArity :: [String]
>     , pfType :: ParseTerm
>     , pfBody :: ParseTerm
>     }
>     deriving Show
>
> type ParseDef = Either ParseInd ParseFun
>
> type ParseBranch = (String, [String], ParseTerm)
>
> type ParseIndRef = (ParseRef, [String])
>
> type Parser a = Parsec String () a
>
> opBegin :: Parser Char
> opBegin = oneOf " -"
> 
> genParser :: GenTokenParser String () Identity
> genParser = makeTokenParser $ LanguageDef
>     { commentStart = "{-"
>     , commentEnd = "-}"
>     , commentLine = "--"
>     , nestedComments = True
>     , identStart = letter <|> char '_'
>     , identLetter = alphaNum <|> char '_' <|> char '\''
>     , opStart = opBegin
>     , opLetter = oneOf " ->="
>     , reservedNames = ["module", "import", "export", "qualified", "as", "data", "where", "forall", "prod", "let", "in", "Prop", "Type", "match", "in", "with", "return", "end"]
>     , reservedOpNames = ["->", " "]
>     , caseSensitive = True
>     }
>
> ident = identifier genParser
> sym = symbol genParser
> kw = reserved genParser
> op = reservedOp genParser
> paren = parens genParser
> nat = fromInteger <$> natural genParser
>
> upperIdent :: Parser String
> upperIdent = try $ do
>     i <- ident
>     if upperString i
>      then return i
>      else fail "Identifier is not uppercase!"
>     where
>         upperString [] = False
>         upperString (x:_) = isUpper x
>
> modulePath :: Parser Symbol
> modulePath = MkSymbol . reverse <$> sepBy1 upperIdent (try $ dot genParser) 
>
> qlName :: Parser Symbol
> qlName = pure qualName <*> modulePath <* dot genParser <*> ident
>
> importType :: Parser ImportType
> importType = maybe Closed (const Open) <$> optionMaybe (sym "(..)")
>
> importIdent :: Parser (String, ImportType)
> importIdent = liftA2 (,) ident importType
>
> importIdents :: Parser (Map.Map String ImportType)
> importIdents = Map.fromList <$> paren (sepBy importIdent (comma genParser))
>
> qualified :: Parser Qualified
> qualified = maybe NotQualified (const Qualified) <$> optionMaybe (kw "qualified")
>
> asName :: Parser (Maybe Symbol)
> asName = optionMaybe (kw "as" >> modulePath)
>
> import_ :: Parser (Symbol, ModuleImport)
> import_ = do
>     kw "import"
>     q <- qualified
>     m <- modulePath
>     n <- asName
>     is <- importIdents
>     return $ (m, ModuleImport q is n)
> 
> module_ :: Parser Symbol
> module_ = kw "module" >> modulePath
>
> header :: Parser ModuleHeader
> header = liftA2 ModuleHeader module_ (many import_)
>
> lambda :: Parser ()
> lambda = void $ sym "\\" <|> sym "λ"
>
> forall :: Parser ()
> forall = kw "forall" <|> void (sym "∀")
>
> pi :: Parser ()
> pi = kw "prod" <|> void (sym "Π")
>
> prod :: Parser ()
> prod = forall <|> pi
>
> param :: Parser [ParseParam]
> param = paren $ pure combine <*> (many1 ident) <* sym ":" <*> term
>     where combine xs t = [(x,t) | x <- xs]
>
> prop :: Parser Sort
> prop = kw "Prop" >> return Prop
>
> type_ :: Parser Sort
> type_ = pure Type <* kw "Type" <*> nat
>
> qualRef :: Parser ParseRef
> qualRef = SymRef <$> qlName
>
> unqualRef :: Parser ParseRef
> unqualRef = StrRef <$> ident
>
> ref :: Parser ParseRef
> ref = try qualRef <|> unqualRef
>
> arrow :: Parser ()
> arrow = void $ sym "->"
>
> caseBranch :: Parser ParseBranch
> caseBranch = pure (,,) <* sym "|" <*> upperIdent <*> many ident <* arrow <*> term
>
> inductiveRef :: Parser ParseIndRef
> inductiveRef = pure (,) <*> ref <* sym "_" <*> many ident
>
> case_ :: Parser ParseTerm
> case_ = pure Case
>     <* kw "match" <*> term
>     <* kw "as" <*> ident
>     <* kw "in" <*> inductiveRef
>     <* kw "return" <*> term
>     <* kw "with" <*> many caseBranch
>     <* kw "end"
>
> term' :: Parser ParseTerm
> term' = sort <|> prodT <|> abs <|> let_ <|> (Ref <$> ref) <|> case_ <|> paren term
>     where
>         sort = Sort <$> (prop <|> type_)
>         gen k f = pure (flip (foldr f)) <* k <*> param <* dot genParser <*> term
>         prodT = gen prod Prod
>         abs = gen lambda Abs
>         let_ = pure (curry Let) <* kw "let" <*> ident <* sym "=" <*> term <* kw "in" <*> term
>
> opTable :: OperatorTable String () Identity ParseTerm
> opTable =
>     [ [ Infix (do { safeWhite >> pure App }) AssocLeft ]
>     , [ Infix (do { arrow >> whiteSpace genParser >> pure (Prod . ("_",)) }) AssocRight ]
>     ]
>     where safeWhite = whiteSpace genParser *> notFollowedBy opBegin
>
> term = buildExpressionParser opTable term'
>
> params :: Parser [ParseParam]
> params = concat <$> many param
>
> collectArity :: ParseTerm -> Parser ([ParseParam], Sort)
> collectArity (Prod l r) = first (l:) <$> collectArity r
> collectArity (Sort s) = return ([], s)
> collectArity _ = fail "Invalid arity declaration!"
>
> indBranch :: String -> Parser ParseConstr
> indBranch i = pure ParseConstr
>     <* sym "|" <*> ident <*> params
>     <* sym ":" <* sym i <*> many term'
>
> inductive :: Parser (String, ParseInd)
> inductive = do
>     kw "data"
>     name <- ident
>     ps <- params
>     sym ":"
>     (ar, s) <- term >>= collectArity
>     kw "where"
>     cs <- many (indBranch name)
>     kw "end"
>     return $ (name, ParseInd name ps ar s cs)
>
> function :: Parser (String, ParseFun)
> function = do
>    name <- ident
>    sym ":"
>    t <- term
>    kw "where"
>    sym name
>    ps <- many ident
>    sym "="
>    bt <- term
>    kw "end"
>    return $ (name, ParseFun name ps t bt)
>
> definition :: Parser (String, ParseDef)
> definition = (second Left <$> inductive) <|> (second Right <$> function)
>
> parseHeader :: String -> String -> Either ParseError (ModuleHeader, String)
> parseHeader = runP (liftA2 (,) header (many anyToken)) ()
>
> parseDefs :: String -> String -> Either ParseError [(String, ParseDef)]
> parseDefs = runP (header *> many definition <* eof) ()
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
> data VarSize = Original | SmallerThan String | Unknown deriving Show
>
> data ResolveParam = Self | Placeholder
>
> type ResolveTerm = S.ParamTerm ResolveParam
>
> instantiate
>     :: (MonadWriter [(k, S.ParamTerm k)] m,  MonadUnify k (S.ParamTerm k) m)
>     => S.Term -> S.Term -> ResolveTerm -> m (S.ParamTerm k)
> instantiate self f = traverse inst
>     where
>         type_ Placeholder x = fresh >>= \t -> tell [(x, S.Param t)]
>         type_ Self x = bind x (parameterize f) >> tell [(x, parameterize self)]
>         inst rp = do
>             x <- fresh
>             type_ rp x
>             return x
>
> elaborate :: MonadResolver m => S.Term -> S.Term -> ResolveTerm -> m S.Term
> elaborate self f rt =
>     do
>         env <- parameterizeAll <$> asks reEnv
>         let e = runInferU (InferEnv env Map.empty) elab
>         liftEither $ first ElaborateFailed e
>     where
>         elab :: InferU String S.Term
>         elab = runUnifyT $ do
>             (pt, ts) <- runWriterT $ instantiate self f rt
>             local (setParams $ Map.fromList ts) $ infer pt
>             pt' <- reify pt
>             maybe (throwError TypeError) return $ strip pt' 
>
> varParent :: VarSize -> Maybe String
> varParent (SmallerThan s) = Just s
> varParent _ = Nothing
>
> data ResolveEnv = ResolveEnv
>     { reVars :: [(String, VarSize)]
>     , reHeader :: ModuleHeader
>     , reCurrentFun :: Maybe ParseFun
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
> withFun :: MonadReader ResolveEnv m => ParseFun -> m a -> m a
> withFun f = local $ \re -> re { reCurrentFun = Just f }
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
> lookupVar :: MonadReader ResolveEnv m => String -> m (Maybe Int)
> lookupVar s = asks (elemIndex s . map fst . reVars)
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
> emitFix :: MonadResolver m => String -> Fixpoint -> m ()
> emitFix s f = emitExport s (FixExport f)
>
> emitFunOrFix :: MonadResolver m => String -> Either Fixpoint Function -> m ()
> emitFunOrFix s e = emitExport s $ either FixExport FunExport e
>
> emitDef :: MonadResolver m => String -> Definition -> m ()
> emitDef s d = modify $ \rs -> rs { rsDefs = Map.insert s d $ rsDefs rs }
>
> emitConstructors :: MonadResolver m => Inductive -> m ()
> emitConstructors i = zipWithM_ emitConstructor [0..] (iConstructors i)
>     where emitConstructor ci c = emitExport (cName c) (ConExport i ci)
>
> exportToTerm :: Export -> S.Term
> exportToTerm e = case eVariant e of
>     FunExport f -> S.Fun f
>     ConExport i ci -> S.Constr i ci
>     IndExport i -> S.Ind i
>     FixExport f -> S.Fix f
> 
> narrowExports :: MonadResolver m => [Export] -> m Export
> narrowExports [] = throwError UnknownReference
> narrowExports [x] = return x
> narrowExports _ = throwError AmbiguousReference
>
> smallerParams :: [Maybe (String, VarSize)] -> Set.Set String
> smallerParams mps = Set.fromList $ catMaybes $ map (>>=(varParent . snd)) mps
>
> recordFixpoint :: MonadResolver m => String -> ParseFun -> m ()
> recordFixpoint s f
>     | s /= pfName f = return ()
>     | otherwise = do
>         params <- take (length $ pfArity f) <$> asks reApps
>         smallerParams <- smallerParams <$> mapM termSize params
>         emitDecreasing smallerParams
> 
> lookupUnqual :: MonadResolver m => String -> m S.Term
> lookupUnqual s = do
>     asks reCurrentFun >>= maybe (return ()) (recordFixpoint s)
>     es <- gets (fromMaybe [] . Map.lookup (unqualName s) . sUnqualified . rsScope)
>     exportToTerm <$> narrowExports es
>
> lookupQual :: MonadResolver m => Symbol -> m S.Term
> lookupQual s = do
>     me <- gets (Map.lookup s . sQualified . rsScope)
>     maybe (throwError UnknownReference) (return . exportToTerm) me
>
> lookupRef :: MonadResolver m => ParseRef -> m S.Term
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
> resolveBranch :: MonadResolver m => VarSize -> ParseBranch -> m (String, S.Term)
> resolveBranch vs (s, ps, t) = (,) s <$> withSizedVars vs ps (resolveTerm t)
>
> matchBranch :: MonadResolver m => [(String, S.Term)] -> Constructor -> m S.Term
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
> resolveTerm :: MonadResolver m => ParseTerm -> m S.Term
> resolveTerm (Ref (StrRef s)) = do
>     vref <- lookupVar s
>     case vref of
>         Just i -> return $ (S.Ref i)
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
> createFunOrFix :: MonadResolver m => [String] -> Function -> m (Either Fixpoint Function)
> createFunOrFix args f = do
>     dec <- fmap (decreasingIndices args . Set.toList) <$> gets rsDecreasing
>     case dec of
>         Just (x:_) -> return $ Left $ Fixpoint f x
>         Just [] -> throwError InvalidFixpoint
>         _ -> return $ Right f
>
> allExplicit :: [S.ParamTerm a] -> [(ParamType, S.ParamTerm a)]
> allExplicit = map ((,) Explicit)
>
> resolveFun :: MonadResolver m => ParseFun -> m DefinitionContent
> resolveFun f = do
>     fts <- resolveTerm (pfType f)
>     (ats, rt) <- liftEither $ collectFunArgs (pfArity f) fts
>     rec f' <- withNoDecreasing $ withRefs ats $ withFun f $ emitFunOrFix (pfName f) f' >> do
>          fb <- withSizedVars Original (pfArity f) $ resolveTerm (pfBody f)
>          fb' <- elaborate fts (either S.Fix S.Fun f') (parameterize fb)
>          createFunOrFix (pfArity f) $ Function (pfName f) (allExplicit ats) rt fb'
>     return $ either FixDef FunDef f'
>
> collectFunArgs :: [String] -> S.Term -> Either ResolveError ([S.Term], S.Term)
> collectFunArgs [] t = return $ ([], t)
> collectFunArgs (_:xs) (S.Prod l r) = first (l:) <$> collectFunArgs xs r
> collectFunArgs _ _ = throwError InvalidArity
>
> resolveParams :: MonadResolver m => [ParseParam] -> m [S.Term]
> resolveParams = foldr (\(x, t) m -> liftA2 (:) (resolveTerm t) (withVar x m)) (return [])
>
> resolveWithParams :: MonadResolver m => [ParseParam] -> m a -> m ([S.Term], a)
> resolveWithParams ps m = foldr (\(x, t) m -> liftA2 (first . (:)) (resolveTerm t) (withVar x m)) ((,) [] <$> m) ps
>
> resolveConstr :: MonadResolver m => ParseConstr -> m S.Constructor
> resolveConstr pc = do
>     ps' <- resolveParams (pcParams pc)
>     is' <- withVars (fst $ unzip $ pcParams pc) $ mapM resolveTerm (pcIndices pc)
>     return $ Constructor (allExplicit ps') is' (pcName pc)
>
> resolveInd :: MonadResolver m => ParseInd -> m S.Inductive
> resolveInd pi = do
>     (ps', is') <- splitAt (length $ piParams pi) <$> resolveParams (piParams pi ++ piArity pi)
>     rec i' <- withRefs ps' $ emitInd (piName pi) i' >> do
>          cs <- withVars (map fst $ piParams pi) $ mapM resolveConstr (piConstructors pi)
>          return $ Inductive (allExplicit ps') is' (piSort pi) cs (piName pi)
>     emitConstructors i'
>     return i'
> 
> resolveDef :: MonadResolver m => ParseDef -> m Definition
> resolveDef d = do
>     dc <- either (fmap IndDef . resolveInd) resolveFun d
>     let def = Definition Public dc
>     emitDef (dName def) def
>     return def
>
> resolveDefs :: ModuleHeader -> GlobalScope -> [(String, ParseDef)] -> Either ResolveError (Map.Map String Definition)
> resolveDefs mh gs ps = (rsDefs . snd) <$> (runExcept $ runReaderT (runStateT (mapM (resolveDef . snd) ps) state) env)
>     where
>         env = ResolveEnv { reVars = [], reHeader = mh, reCurrentFun = Nothing, reApps = [], reEnv = [] }
>         state = ResolveState { rsScope = gs, rsDefs = Map.empty, rsDecreasing = Nothing }
