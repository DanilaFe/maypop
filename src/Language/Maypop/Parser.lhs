In this module, we'll write a Parsec-based parser for the Maypop language.
No explanations for now, this is long, subject to change, and kind of
repetitive.

> {-# LANGUAGE TupleSections #-}
> {-# LANGUAGE FlexibleContexts #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE UndecidableInstances #-}
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
> import Text.Parsec.Expr
> import Text.Parsec.Indent
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
> type Parser a = IndentParser String () a
>
> opBegin :: Parser Char
> opBegin = oneOf " -"
> 
> genParser :: GenTokenParser String () (IndentT Identity)
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
> blk a = (indented >> block a) <|> return []
> ident = identifier genParser
> sym = symbol genParser
> kw = reserved genParser
> op = reservedOp genParser
> paren = parens genParser
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
> type_ = pure Type <* kw "Type" <*> (fromInteger <$> natural genParser)
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
> caseBranch = withPos $ pure (,,) <*> upperIdent <*> many ident <* arrow <*> term
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
>     <* kw "with" <*> blk caseBranch
>
> nat :: Parser ParseTerm
> nat = (foldr App (natRef "O") . (`replicate` (natRef "S")) . fromInteger) <$> natural genParser
>     where natRef s = Ref (SymRef (MkSymbol [s, "Nat", "Data"]))
>
> list :: Parser ParseTerm
> list = do
>     (ts, t) <- brackets genParser $ (,) <$> commaSep genParser term <* sym ":" <*> term
>     let listRef s = Ref (SymRef (MkSymbol [s, "List", "Data"]))
>     let cons = App (listRef "Cons") t
>     let nil = App (listRef "Nil") t
>     return $ foldr (\x xs -> App (App cons x) xs) nil ts
> 
> term' :: Parser ParseTerm
> term' = indented >> (sort <|> prodT <|> abs <|> let_ <|> (Ref <$> ref) <|> case_ <|> nat <|> list <|> paren term)
>     where
>         sort = Sort <$> (prop <|> type_)
>         gen k f = pure (flip (foldr f)) <* k <*> param <* dot genParser <*> term
>         prodT = gen prod Prod
>         abs = gen lambda Abs
>         let_ = pure (curry Let) <* kw "let" <*> ident <* sym "=" <*> term <* kw "in" <*> term
>
> opTable :: OperatorTable String () (IndentT Identity) ParseTerm
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
> indBranch i = withPos $ pure ParseConstr
>     <*> ident <*> params
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
>     cs <- blk (indBranch name)
>     return $ (name, ParseInd name ps ar s cs)
>
> function :: Parser (String, ParseFun)
> function = do
>    name <- ident
>    sym ":"
>    t <- term
>    sym name
>    ps <- many ident
>    sym "="
>    bt <- term
>    return $ (name, ParseFun name ps t bt)
>
> definition :: Parser (String, ParseDef)
> definition = (second Left <$> inductive) <|> (second Right <$> function)
>
> parseHeader :: String -> String -> Either ParseError (ModuleHeader, String)
> parseHeader fn s = runIdentity $ runIndentParserT (liftA2 (,) header (many anyToken)) () fn s
>
> parseDefs :: String -> String -> Either ParseError [(String, ParseDef)]
> parseDefs fn s = runIdentity $ runIndentParserT (header *> many definition <* eof) () fn s
