module Parser.String where

import qualified Text.ParserCombinators.Parsec          as P
import qualified Text.ParserCombinators.Parsec.Language as Language
import qualified Text.ParserCombinators.Parsec.Token    as Token

import qualified RawAST                                 as R
import qualified Types                                  as T

type Parser = P.Parser

parse :: Parser a -> String -> Either P.ParseError a
parse p s = P.parse p "" s

languageDef :: Token.LanguageDef st
languageDef =
  Language.emptyDef { Token.commentStart    = "/*"
           , Token.commentEnd      = "*/"
           , Token.commentLine     = "//"
           , Token.identStart      = P.lower
           , Token.identLetter     = P.lower P.<|> P.char '.'
           , Token.reservedNames   = [ "IF"
                                     , "WHILE"
                                     , "ALT"
                                     , "SEQ"
                                     , "PAR"
                                     , "FOR"
                                     , "TO"
                                     , "()"
                                     , "TRUE" , "FALSE"
                                     , "SKIP", "STOP"
                                     , "INT", "CHAR", "BOOL", "UNIT", "CHAN", "VAR", "VAL"
                                     , "tim", "AFTER"
                                     , "FUNCTION", "PROC"
                                     , "STATIC"
                                     , "len"
                                     ]
           , Token.reservedOpNames = ["+", "-", "*", "/", "=", "==", "!", "&"
                                     , "<", ">", ">=", "<=", "&&", "||", "?", ":", "%"
                                     ]
           , Token.caseSensitive = False
           }

lexer :: Token.TokenParser st
lexer = Token.makeTokenParser languageDef

identifier :: Parser String
identifier = Token.identifier lexer -- parses an identifier
reserved :: String -> Parser ()
reserved   = Token.reserved   lexer -- parses a reserved name
reservedOp :: String -> Parser ()
reservedOp = Token.reservedOp lexer -- parses an operator
parens :: Parser a -> Parser a
parens     = Token.parens     lexer -- parses surrounding parenthesis
brackets :: Parser a -> Parser a
brackets   = Token.brackets   lexer
comma :: Parser ()
comma      = () <$ Token.comma      lexer -- parse a ", " and whiteP.space
integer :: Parser Integer
integer    = Token.integer    lexer -- parses an integer
whiteSpace :: Parser ()
whiteSpace = Token.whiteSpace lexer -- parses whitespace

parseLiteral :: Parser R.Literal
parseLiteral =  fmap (const R.UnitLit) (reserved "()")
          P.<|> fmap (const $ R.BoolLit True) (reserved "TRUE")
          P.<|> fmap (const $ R.BoolLit False) (reserved "FALSE")
          P.<|> fmap R.CharLit (Token.charLiteral lexer)
          P.<|> fmap (R.IntLit . fromInteger) integer
          P.<|> fmap R.ArrLit (Token.brackets lexer $ P.sepBy1 parseLiteral comma)

exprList :: Parser [R.Expr]
exprList = parens $ P.sepBy1 expr comma

parseFunc :: Parser R.FCall
parseFunc = do ident <- identifier
               params <- parens (P.sepBy expr comma)
               return $ R.FCall ident params

data Unary = NEG | NOT
data Binary = ADD | MINUS | MUL | DIV | MOD | AND | OR | CEQ | CGT | CGTE
data Ternary = TIF

uPrecedence :: Unary -> (Int, R.Expr -> R.Expr)
uPrecedence NEG = (5, R.Monop R.Neg)
uPrecedence NOT = (5, R.Monop R.Not)

bPrecedence :: Binary -> (Int, R.Expr -> R.Expr -> R.Expr)
bPrecedence ADD = (2, R.Binop R.Add)
bPrecedence MINUS = (2, R.Binop R.Minus)
bPrecedence MUL = (3, R.Binop R.Mul)
bPrecedence DIV = (3, R.Binop R.Div)
bPrecedence MOD = (3, R.Binop R.Mod)
bPrecedence AND = (0, R.Binop R.And)
bPrecedence OR = (0, R.Binop R.Or)
bPrecedence CEQ = (1, R.Binop R.CompareEQ)
bPrecedence CGT = (1, R.Binop R.CompareGT)
bPrecedence CGTE = (1, R.Binop R.CompareGTE)

tPrecedence :: Ternary -> (Int, R.Expr -> R.Expr -> R.Expr -> R.Expr)
tPrecedence TIF = (4, R.ExprIf)

unary :: Parser Unary
unary = (fmap (const NOT) $ reservedOp "!") P.<|> (fmap (const NEG) $ reservedOp "-")

binary :: Parser Binary
binary = (ADD <$ reservedOp "+")
   P.<|> (MINUS <$ reservedOp "-")
   P.<|> (MUL <$ reservedOp "*")
   P.<|> (DIV <$ reservedOp "/")
   P.<|> (MOD <$ reservedOp "%")
   P.<|> (AND <$ reservedOp "&&")
   P.<|> (OR <$ reservedOp "||")
   P.<|> (CEQ <$ reservedOp "==")
   P.<|> (CGTE <$ reservedOp ">=")
   P.<|> (CGT <$ reservedOp ">")

expr :: Parser R.Expr
expr = exprHelper 0

exprHelper :: Int -> Parser R.Expr
exprHelper n = unaryHelper >>= loop
               where
                 loop :: R.Expr -> Parser R.Expr
                 loop e = do m_f <- P.optionMaybe (binaryHelper n)
                             case m_f of
                               Nothing -> return e
                               Just Nothing -> return e
                               Just (Just f) -> loop (f e)

unaryHelper :: Parser R.Expr
unaryHelper = parens expr
        P.<|> identHelper
        P.<|> (unary >>= (\u -> case uPrecedence u of
                                (n, f) -> fmap f (exprHelper n)))
        P.<|> fmap R.Lit parseLiteral

binaryHelper :: Int -> Parser (Maybe (R.Expr -> R.Expr))
binaryHelper n = (do (k, f) <- (P.lookAhead . P.try $ binary >>= (return . bPrecedence))
                     if k < n then return Nothing
                              else do _ <- binary -- actually consume the input
                                      e <- exprHelper (k)
                                      return . Just $ flip f e)
             P.<|> (reservedOp "?" >> expr >>= (\e ->
                    reservedOp ":" >> exprHelper n >>= (\f -> return . Just $ (\test -> R.ExprIf test e f))
                ))

identHelper :: Parser R.Expr
identHelper = (do reserved "len"
                  fmap R.Length $ parens refHelper)
              P.<|>
              (do ident <- identifier
                  m_f_params <- P.optionMaybe (parens $ P.sepBy expr comma)
                  case m_f_params of
                    Just params -> return $ R.CallFunction (R.FCall ident params)
                    Nothing -> do indexes <- P.many (brackets expr)
                                  return $ R.Lookup (R.Ref ident indexes))

refHelper :: Parser R.Ref
refHelper = do ident <- identifier
               indexes <- P.many (brackets expr)
               return $ R.Ref ident indexes

parseString :: String -> R.Expr
parseString str =
  case P.parse expr "" str of
    Left e  -> error $ show e
    Right r -> r

parseAssign :: Parser R.Assign
parseAssign = do refs <- P.sepBy1 refHelper comma
                 reservedOp "="
                 exprs <- P.sepBy1 expr comma
                 case exprs of
                   [R.CallFunction f] | length refs > 1 -> return $ Right (R.FAssign refs f)
                   _ -> return . Left $ R.EAssign refs exprs

parseBaseTy :: Parser T.BaseTy
parseBaseTy = T.UnitTy <$ (reserved "UNIT")
          P.<|> T.BoolTy <$ (reserved "BOOL")
          P.<|> T.CharTy <$ (reserved "CHAR")
          P.<|> T.IntTy <$ (reserved "INT")

parseVarDecl :: Parser R.VarDecl
parseVarDecl = do base_ty <- parseBaseTy
                  name <- identifier
                  dimens <- P.many (brackets $ expr)
                  let ty = iterate T.Arr (T.Base base_ty) !! length dimens
                  return $ R.VarDecl name ty dimens

parseVarDecls :: Parser [R.VarDecl]
parseVarDecls = P.sepBy1 parseVarDecl comma

parseChanDecl :: Parser R.ChanDecl
parseChanDecl = do base_ty <- parseBaseTy
                   reserved "CHAN"
                   name <- identifier
                   dimens <- P.many (brackets $ expr)
                   let ty = iterate T.ChanArr (T.ChanBoth base_ty) !! length dimens
                   return $ R.ChanDecl name ty dimens

parseChanDecls :: Parser [R.ChanDecl]
parseChanDecls = P.sepBy1 parseChanDecl comma

parseRepl :: String -> Parser (Maybe (T.Ident, R.Expr, R.Expr))
parseRepl s = reserved s >>
                  ((do ident <- identifier
                       reserved "FOR"
                       e1 <- expr
                       reserved "TO"
                       e2 <- expr
                       return $ Just (ident, e1, e2))
                   P.<|> return Nothing)

parseGuard :: Parser (R.Expr, R.Guard)
parseGuard = do e <- expr
                reservedOp "&"
                (P.<|>) (do reserved "tim"
                            reservedOp "?"
                            reserved "AFTER"
                            fmap (\t -> (e, R.TimGuard t)) expr)
                        ((P.<|>) (reserved "SKIP" >> return (e, R.SkipGuard))
                                 (do chan_ref <- refHelper
                                     reservedOp "?"
                                     var_ref <- identifier
                                     return $ (e, R.InputGuard chan_ref var_ref)))

parseFuncHeader :: Parser (R.Valof -> R.Function)
parseFuncHeader = do out_types <- P.sepBy parseBaseTy comma
                     reserved "FUNCTION"
                     ident <- identifier
                     in_types <- parens $ P.sepBy in_param comma
                     return $ R.Function out_types ident in_types
                  where
                   in_param :: Parser R.FunctionParam
                   in_param = do reserved "VAL"
                                 base_ty <- parseBaseTy
                                 ident <- identifier
                                 return (ident, base_ty)

parseProcHeader :: Parser (R.ProcBody -> R.Procedure)
parseProcHeader = do reserved "PROC"
                     ident <- identifier
                     in_types <- parens $ P.sepBy in_param comma
                     return $ R.Procedure ident in_types
                  where
                    in_param :: Parser (T.Ident, T.ProcArg)
                    in_param = (do reserved "VAR"
                                   num <- fmap length (P.many $ P.string "[]")
                                   ty <- parseBaseTy
                                   ident <- identifier
                                   let wrapped_ty = iterate T.Arr (T.Base ty) !! num
                                   return (ident, T.ProcVar wrapped_ty))
                         P.<|> (do reserved "VAL"
                                   ty <- parseBaseTy
                                   ident <- identifier
                                   return (ident, T.ProcConst ty))
                         P.<|> (do reserved "CHAN"
                                   num <- fmap length (P.many $ P.string "[]")
                                   ty <- parseBaseTy
                                   ident <- identifier
                                   ty_dir <- (T.ChanOutput ty <$ reservedOp "!") P.<|> (T.ChanInput ty <$ reservedOp "?")
                                   let wrapped_ty = iterate T.ChanArr ty_dir !! num
                                   return (ident, T.ProcChan wrapped_ty)
                               )

parseQuerySend :: Parser R.ProcBody
parseQuerySend = (do reserved "screen"
                     reservedOp "!"
                     e <- expr
                     return $ R.Screen e)
                 P.<|>
                 (do reserved "keyboard"
                     reservedOp "?"
                     var <- refHelper
                     return $ R.Key var)
                 P.<|>
                 (do ref <- refHelper
                     (P.<|>) (do reservedOp "!"
                                 e <- expr
                                 return $ R.Send ref e)
                             (do reservedOp "?"
                                 var <- refHelper
                                 return $ R.Query ref var))

parseSkipCall :: Parser R.ProcBody
parseSkipCall = (R.Skip <$ reserved "SKIP")
          P.<|> (do ident <- identifier
                    params <- parens $ P.sepBy expr comma
                    return $ R.Call ident params)

parseStatic :: Parser R.Static
parseStatic = do reserved "STATIC"
                 (P.<|>) (do reserved "VAL"
                             num <- fmap length $ P.many $ P.string "[]"
                             ty <- parseBaseTy
                             ident <- identifier
                             reserved "="
                             lit <- (parseLiteral P.<|> (fmap (R.ArrLit . map R.CharLit) $ Token.stringLiteral lexer))
                             let wrapped_ty = iterate T.Arr (T.Base ty) !! num
                             return $ R.Static ident (R.StaticVal wrapped_ty lit))
                         (do reserved "CHAN"
                             size <- P.many $ brackets $ fmap fromInteger integer
                             ty <- parseBaseTy
                             ident <- identifier
                             return $ R.Static ident (R.StaticChan size ty))

