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
> import Control.Applicative hiding ((<|>), many)
> import Control.Monad.Reader
> import Control.Monad.State
> import Control.Monad.Except
> import Text.Parsec
> import Text.Parsec.Token
> import Text.Parsec.Char
> import Text.Parsec.Expr
> import Text.Parsec.Combinator
> import qualified Data.Map as Map
> import Data.Foldable
> import Data.Char
> import Data.Bifunctor
> import Data.List
> import Data.Maybe
> import Data.Functor.Identity
> import Debug.Trace
>
>
> data ParseRef = SymRef Symbol | StrRef String
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
>
> data ParseConstr = ParseConstr
>     { pcName :: String
>     , pcParams :: [ParseParam]
>     , pcIndices :: [ParseTerm]
>     }
>
> data ParseInd = ParseInd
>     { piName :: String
>     , piParams :: [ParseParam] 
>     , piArity :: [ParseParam]
>     , piSort :: Sort
>     , piConstructors :: [ParseConstr]
>     }
>
> data ParseFun = ParseFun
>     { pfName :: String
>     , pfArity :: [String]
>     , pfType :: ParseTerm
>     , pfBody :: ParseTerm
>     }
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
>         upperString (x:xs) = isUpper x
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
> param :: Parser ParseParam
> param = paren $ pure (,) <*> ident <* sym ":" <*> term
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
>         gen k f = pure f <* k <*> param <* dot genParser <*> term
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
> params = many param
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
>     deriving Show
>
> data ResolveEnv = ResolveEnv
>     { reVars :: [String]
>     , reHeader :: ModuleHeader
>     }
>
> withVar :: MonadReader ResolveEnv m => String -> m a -> m a
> withVar s = local (\re -> re { reVars = s : reVars re })
>
> withVars :: MonadReader ResolveEnv m => [String] -> m a -> m a
> withVars xs m = foldr withVar m xs
>
> currentModule :: MonadReader ResolveEnv m => m Symbol
> currentModule = asks (mhName . reHeader)
>
> lookupVar :: MonadReader ResolveEnv m => String -> m (Maybe Int)
> lookupVar s = asks (elemIndex s . reVars)
>
> data ResolveState = ResolveState
>     { rsScope :: GlobalScope
>     , rsDefs :: Map.Map String Definition
>     }
>
> class (MonadReader ResolveEnv m, MonadState ResolveState m, MonadError ResolveError m, MonadFix m)
>     => MonadResolver m where
>
> instance (MonadReader ResolveEnv m, MonadState ResolveState m, MonadError ResolveError m, MonadFix m)
>     => MonadResolver m where
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
> exportToTerm :: Export -> S.Term
> exportToTerm e = case eVariant e of
>     FunExport f -> S.Fun f
>     ConExport i ci -> S.Constr i ci
>     IndExport i -> S.Ind i
> 
> narrowExports :: MonadResolver m => [Export] -> m Export
> narrowExports [] = throwError UnknownReference
> narrowExports [x] = return x
> narrowExports xs = throwError AmbiguousReference
>
> lookupUnqual :: MonadResolver m => String -> m S.Term
> lookupUnqual s = do
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
> resolveBranch :: MonadResolver m => ParseBranch -> m (String, S.Term)
> resolveBranch (s, ps, t) = (,) s <$> withVars ps (resolveTerm t)
>
> matchBranch :: MonadResolver m => [(String, S.Term)] -> Constructor -> m S.Term
> matchBranch bs c = maybe (throwError IncompleteMatch) return $ lookup (cName c) bs 
>
> resolveTerm :: MonadResolver m => ParseTerm -> m S.Term
> resolveTerm (Ref (StrRef s)) = do
>     vref <- lookupVar s
>     case vref of
>         Just i -> return $ (S.Ref i)
>         Nothing -> lookupUnqual s
> resolveTerm (Ref (SymRef s)) = lookupQual s
> resolveTerm (Abs (x, tt) t) = liftA2 S.Abs (resolveTerm tt) (withVar x $ resolveTerm t)
> resolveTerm (App l r) = liftA2 S.App (resolveTerm l) (resolveTerm r)
> resolveTerm (Let (x, t) ti) = liftA2 S.Let (resolveTerm t) (withVar x $ resolveTerm ti)
> resolveTerm (Prod (x, tt) t) = liftA2 S.Prod (resolveTerm tt) (withVar x $ resolveTerm t)
> resolveTerm (Sort s) = return $ S.Sort s
> resolveTerm (Case t x ir tt bs) = do
>     t' <- resolveTerm t
>     (i, is) <- resolveIndRef ir
>     tt' <- withVars (x:is) $ resolveTerm tt
>     bs' <- mapM resolveBranch bs
>     cbs <- mapM (matchBranch bs') $ iConstructors i
>     return $ S.Case t' i tt' cbs
>
> resolveFun :: MonadResolver m => ParseFun -> m S.Function
> resolveFun f = do
>     fts <- resolveTerm (pfType f)
>     (ats, rt) <- liftEither $ collectFunArgs (pfArity f) fts
>     rec f' <- emitFun (pfName f) f' >> do
>          fb <- withVars (pfArity f) $ resolveTerm (pfBody f)
>          return $ Function (pfName f) ats rt fb
>     return f'
>
> collectFunArgs :: [String] -> S.Term -> Either ResolveError ([S.Term], S.Term)
> collectFunArgs [] t = return $ ([], t)
> collectFunArgs (_:xs) (S.Prod l r) = first (l:) <$> collectFunArgs xs r
> collectFunArgs l _ = throwError InvalidArity
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
>     return $ Constructor ps' is' (pcName pc)
>
> resolveInd :: MonadResolver m => ParseInd -> m S.Inductive
> resolveInd pi = do
>     (ps', is') <- splitAt (length $ piParams pi) <$> resolveParams (piParams pi ++ piArity pi)
>     rec i' <- emitInd (piName pi) i' >> do
>          cs <- withVars (map fst $ piParams pi) $ mapM resolveConstr (piConstructors pi)
>          return $ Inductive ps' is' (piSort pi) cs (piName pi)
>     emitConstructors i'
>     return i'
> 
> resolveDef :: MonadResolver m => ParseDef -> m Definition
> resolveDef d = do
>     dc <- either (fmap Left . resolveInd) (fmap Right . resolveFun) d
>     let def = Definition Public dc
>     emitDef (dName def) def
>     return def
>
> resolveDefs :: ModuleHeader -> GlobalScope -> [(String, ParseDef)] -> Either ResolveError (Map.Map String Definition)
> resolveDefs mh gs ps = (rsDefs . snd) <$> (runExcept $ runReaderT (runStateT (mapM (resolveDef . snd) ps) state) env)
>     where
>         env = ResolveEnv { reVars = [], reHeader = mh }
>         state = ResolveState { rsScope = gs, rsDefs = Map.empty }
