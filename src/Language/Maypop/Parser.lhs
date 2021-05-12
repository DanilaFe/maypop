In this module, we'll write a Parsec-based parser for the Maypop language.

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
> import Data.Char

> data ParseEnv = ParseEnv
>     { peVars :: Map.Map String Int
>     }
> 
> extendEnv :: String -> ParseEnv -> ParseEnv
> extendEnv s e = e { peVars = Map.insert s 0 $ Map.map (+1) $ peVars e }

> data ParseState = ParseState
>     { psDefs :: Map.Map String Definition
>     , psScope :: GlobalScope
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
>     , reservedNames = ["module", "import", "export", "qualified", "as", "data", "where", "forall", "prod", "let", "in", "Prop", "Type", "case", "of"]
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
> importIdents = Map.fromList <$> paren (sepBy1 importIdent (comma genParser))
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
> param = pure (,) <*> ident <* sym ":" <*> term
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
> term' :: Parser Term
> term' = sort <|> prodT <|> abs <|> let_ <|> ref <|> paren term
>     where
>         sort = Sort <$> (prop <|> type_)
>         gen k f = do
>             k
>             (s, t1) <- param
>             dot genParser
>             t2 <- local (extendEnv s) term
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
>             t2 <- local (extendEnv s) term
>             return $ Let t1 t2
>
> term = foldl1 App <$> many1 term'
>
> run :: Parser a -> String -> Either ParseError a
> run p s = runReader (runPT p (ParseState Map.empty emptyScope) "<test>" s) (ParseEnv Map.empty)
