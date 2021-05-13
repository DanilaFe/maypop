In this module, we'll write a Parsec-based parser for the Maypop language.
No explanations for now, this is long, subject to change, and kind of
repetitive.

> module Language.Maypop.Parser where
> import Prelude hiding (pi)
> import Language.Maypop.Syntax
> import Language.Maypop.Modules
> import Control.Applicative hiding ((<|>), many)
> import Control.Monad.Reader
> import Text.Parsec
> import Text.Parsec.Token
> import Text.Parsec.Char
> import Text.Parsec.Combinator
> import qualified Data.Map as Map
> import Data.Foldable
> import Data.Char
> import Data.Bifunctor
>
> data ParseEnv = ParseEnv
>     { peVars :: Map.Map String Int
>     , peHeader :: Maybe ModuleHeader
>     }
> 
> extendEnv :: String -> ParseEnv -> ParseEnv
> extendEnv s e = e { peVars = Map.insert s 0 $ Map.map (+1) $ peVars e }
>
> extend :: String -> Parser a -> Parser a
> extend = local . extendEnv
>
> extendMany :: [String] -> Parser a -> Parser a
> extendMany ss e = foldr extend e ss
>
> requireHeader :: Parser ModuleHeader
> requireHeader = asks peHeader >>= maybe (fail "Header required but not yet processed!") return
>
> requireModuleName :: Parser Symbol
> requireModuleName = mhName <$> requireHeader
>
> data ParseState = ParseState
>     { psScope :: GlobalScope
>     }
>
> type Parser a = ParsecT String ParseState (Reader ParseEnv) a
>
> genParser :: GenTokenParser String ParseState (Reader ParseEnv)
> genParser = makeTokenParser $ LanguageDef
>     { commentStart = "{-"
>     , commentEnd = "-}"
>     , commentLine = "--"
>     , nestedComments = True
>     , identStart = letter <|> char '_'
>     , identLetter = alphaNum <|> char '_' <|> char '\''
>     , opStart = oneOf "-"
>     , opLetter = oneOf "->="
>     , reservedNames = ["module", "import", "export", "qualified", "as", "data", "where", "forall", "prod", "let", "in", "Prop", "Type", "match", "in", "with", "return", "end"]
>     , reservedOpNames = ["->"]
>     , caseSensitive = True
>     }
>
> ident = identifier genParser
> sym = symbol genParser
> kw = reserved genParser
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
> param :: Parser (String, Term)
> param = paren $ pure (,) <*> ident <* sym ":" <*> term
>
> prop :: Parser Sort
> prop = kw "Prop" >> return Prop
>
> type_ :: Parser Sort
> type_ = pure Type <* kw "Type" <*> nat
>
> fromExport :: ExportVariant -> Term
> fromExport (IndExport i) = Ind i
> fromExport (ConExport i ci) = Constr i ci
> fromExport (FunExport f) = Fun f
> 
> qualRef :: Parser Term
> qualRef = do
>     s <- qlName
>     exportRef <- Map.lookup s . sQualified . psScope <$> getState
>     maybe (fail $ "Undefined reference: " ++ show s) (return . fromExport . eVariant) exportRef
>
> resolveUnqual :: [Export] -> Parser Term
> resolveUnqual [] = fail "No matching definitions!"
> resolveUnqual [x] = return $ fromExport $ eVariant x
> resolveUnqual xs = fail $ "Ambigous reference: could be one of " ++ show (map eOriginalModule xs)
>
> unqualRef :: Parser Term
> unqualRef = do
>     s <- ident
>     localRef <- asks (Map.lookup s . peVars)
>     case localRef of
>         Just i -> return $ Ref i
>         Nothing -> do
>             exportRef <- Map.lookup (unqualName s) . sUnqualified . psScope <$> getState
>             maybe (fail $ "Undefined reference: " ++ s) resolveUnqual exportRef
>
> arrow :: Parser ()
> arrow = void $ sym "->" <|> sym "→"
>
> caseBranch :: Parser (String, Term)
> caseBranch = do
>     sym "|"
>     constr <- upperIdent
>     params <- many ident
>     arrow
>     t <- extendMany params term
>     return (constr, t)
>
> inductiveRef :: Parser (Inductive, [String])
> inductiveRef = do
>     ref <- try qualRef <|> unqualRef
>     case ref of
>         Ind i -> do
>              sym "_"
>              ps <- many ident
>              if length ps == length (iArity i)
>               then return (i, ps)
>               else fail "Incorrect inductive arity!"
>         _ -> fail "Not an inductive data type!"
>
> toCaseBranches :: Inductive -> [(String, Term)] -> Parser [Term]
> toCaseBranches i bs = do
>     mapM (\c -> maybe (fail $ "Missing branch " ++ (cName c) ++ " from " ++ show (map fst bs)) return $ (`lookup` bs) $ cName c) (iConstructors i)
>
> case_ :: Parser Term
> case_ = do
>     kw "match"
>     t <- term
>     kw "as"
>     as <- ident
>     kw "in"
>     (i, ps) <- inductiveRef
>     kw "return"
>     tt <- extendMany (as:ps) term 
>     kw "with"
>     bs <- many caseBranch >>= toCaseBranches i
>     kw "end"
>     return $ Case t i tt bs
>
> term' :: Parser Term
> term' = sort <|> prodT <|> abs <|> let_ <|> ref <|> case_ <|> paren term
>     where
>         sort = Sort <$> (prop <|> type_)
>         gen k f = do
>             k
>             (s, t1) <- param
>             dot genParser
>             t2 <- extend s term
>             return $ f t1 t2
>         prodT = gen prod Prod
>         abs = gen lambda Abs
>         ref = unqualRef <|> qualRef
>         let_ = do
>             kw "let"
>             s <- ident
>             sym "="
>             t1 <- term
>             kw "in"
>             t2 <- extend s term
>             return $ Let t1 t2
>
> term = foldl1 App <$> many1 term'
>
> params :: Parser [(String, Term)]
> params =
>     do
>         (s, t) <- param
>         ps <- extend s params
>         return $ (s,t):ps
>     <|> return []
>
> collectArity :: Term -> Parser ([Term], Sort)
> collectArity (Prod l r) = first (l:) <$> collectArity r
> collectArity (Sort s) = return ([], s)
> collectArity _ = fail "Invalid arity declaration!"
>
> indBranch :: String -> Int -> Parser Constructor
> indBranch ind ar = do
>     sym "|"
>     cname <- ident
>     (xs, ps) <- unzip <$> params
>     sym ":"
>     name <- ident
>     indices <- many $ extendMany xs term'
>     if name /= ind || ar /= length indices
>      then fail "Invalid constructor return!"
>      else return $ Constructor ps indices cname
>
> registerExport :: String -> ExportVariant -> Parser ()
> registerExport s ev = do
>     mn <- requireModuleName
>     let e = Export ev mn
>     let gs' = GlobalScope (Map.singleton (qualName mn s) e) (Map.singleton (unqualName s) [e])
>     gs <- psScope <$> getState
>     case mergeScopes gs gs' of
>         Right gs'' -> modifyState (\s -> s { psScope = gs'' })
>         Left _ -> fail $ "Duplicate name: " ++ s
>
> registerInd :: Inductive -> Parser ()
> registerInd i = do
>     registerExport (iName i) (IndExport i)
>     zipWithM_ (\ci c -> registerExport (cName c) (ConExport i ci)) [0..] (iConstructors i)
>
> inductive :: Parser Inductive
> inductive = do
>     kw "data"
>     name <- ident
>     (xs, ps) <- unzip <$> params
>     sym ":"
>     (ar, s) <- extendMany xs term >>= collectArity
>     kw "where"
>     cs <- many (extendMany xs $ indBranch name (length ar))
>     kw "end"
>     let ind = Inductive ps ar s cs name
>     registerInd ind
>     return ind
>
> function :: Parser Function
> function = do
>    name <- ident
>    sym ":"
>    t <- term
>    kw "where"
>    sym name
>    ps <- many ident
>    sym "="
>    bt <- extendMany ps term
>    kw "end"
>    let fun = Function name (length ps) t bt
>    registerExport name (FunExport $ fun)
>    return fun
>
> definition :: Parser Definition
> definition = Definition Public <$> (Left <$> inductive <|> Right <$> function)
>
> definitionMap :: Parser (Map.Map String Definition)
> definitionMap = do
>     defs <- many definition
>     return $ Map.fromList $ map (\d -> (dName d, d)) defs
>
> parseHeader :: String -> String -> Either ParseError (ModuleHeader, String)
> parseHeader file s = runReader (runPT initialParser (ParseState emptyScope) file s) (ParseEnv Map.empty Nothing)
>     where
>         initialParser = liftA2 (,) header (many anyToken)
>
> parseModule :: ModuleHeader -> GlobalScope -> String -> String -> Either ParseError (Map.Map String Definition)
> parseModule mh gs file s = runReader (runPT definitionMap (ParseState gs) file s) (ParseEnv Map.empty (Just mh))
