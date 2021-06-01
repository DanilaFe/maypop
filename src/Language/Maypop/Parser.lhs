In this module, we'll write a Parsec-based parser for the Maypop language.
No explanations for now, this is long, subject to change, and kind of
repetitive.

> {-# LANGUAGE TupleSections #-}
> module Language.Maypop.Parser where
> import Prelude hiding (pi)
> import Language.Maypop.Syntax hiding (ParamTerm(..), Term)
> import Language.Maypop.Modules hiding (function)
> import Control.Applicative hiding ((<|>), many)
> import Control.Monad.Reader
> import Text.Parsec
> import Text.Parsec.Token
> import Text.Parsec.Expr
> import qualified Data.Map as Map
> import Data.Char
> import Data.Bifunctor
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
>     , pfArity :: [(ParamType, String)]
>     , pfType :: ParseTerm
>     , pfBody :: ParseTerm
>     }
>     deriving Show
>
> pfArgNames :: ParseFun -> [String]
> pfArgNames = map snd . pfArity
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
>     , reservedNames = ["module", "import", "export", "qualified", "as", "data", "where", "forall", "prod", "let", "in", "Prop", "Constraint", "Type", "match", "in", "with", "return", "end"]
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
> constraint :: Parser Sort
> constraint = kw "Constraint" >> return Constraint
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
>         sort = Sort <$> (prop <|> constraint <|> type_)
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
> funParam :: Parser (ParamType, String)
> funParam =
>     (sym "{" *> ((,) Inferred <$> ident) <* sym "}") <|> 
>     ((,) Explicit <$> ident)
> 
> function :: Parser (String, ParseFun)
> function = do
>    name <- ident
>    sym ":"
>    t <- term
>    kw "where"
>    sym name
>    ps <- many funParam
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
