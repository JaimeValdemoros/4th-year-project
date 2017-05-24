module Parser.Parse where

import Control.Arrow
import qualified RawAST as R
import qualified Parser.String as S
import qualified Parser.Tree as T

parseIfBranch :: T.Parser T.ProgTree a -> T.Parser T.ProgTree (R.Expr, a)
parseIfBranch p = T.tree (,) S.expr (T.one p)

parseAltBranch :: T.Parser T.ProgTree ((R.Expr, R.Guard), R.ProcBody)
parseAltBranch = T.tree (,) S.parseGuard (T.one parseProc)

parseOptRepl :: String -> T.TreeParser a -> T.TreeParser (R.Repl a)
parseOptRepl label inner = arr T.rootLabel &&& arr T.subForest >>>
                           first (T.stringParser $ S.parseRepl label) >>>
                           Kleisli decide
                           where
                             decide (Nothing, forest) = R.ListRepl <$> T.runParser (T.many1 inner) forest
                             decide (Just (ident, e1, e2), forest) =
                                (R.IndexRepl ident e1 e2) <$> (T.runParser (T.one inner) forest)

parseCommon :: T.Parser T.ProgTree a -> T.Parser T.ProgTree (R.CommonBody a)
parseCommon inj = T.choices choices
                  where
                    choices = [ T.simpleTree $ (R.Assign <$> S.parseAssign)
                              , T.tree (const R.If) (S.reserved "IF")
                                                     (T.many1 $ parseIfBranch parseCommon')
                              , T.tree R.While (S.reserved "WHILE" >> S.expr)
                                               (T.one $ parseCommon')
                              , parseOptRepl "SEQ" parseCommon' >>^ (R.Seq [])
                              , T.tree (\decl (R.Seq [] body) -> R.Seq decl body) (S.parseVarDecls) (T.one $ parseOptRepl "SEQ" parseCommon' >>^ (R.Seq []))
                              , T.simpleTree $ (R.Stop <$ S.reserved "STOP")
                              ]
                    parseCommon' = T.choices (choices ++ [inj >>^ R.Inj])

parseValof :: T.Parser [T.ProgTree] R.Valof
parseValof = (T.forestSnoc (T.one $ parseCommon T.parseFail)
                           (T.simpleTree S.exprList)) >>^ (uncurry (R.Valof []))

parseFunction :: T.Parser T.ProgTree R.Function
parseFunction = T.tree ($) S.parseFuncHeader parseValof

parseAltInner :: T.TreeParser R.InnerAlt
parseAltInner = T.choices [ parseAltBranch >>^ (uncurry . uncurry $ R.AltBranch)
                          , parseOptRepl "ALT" parseAltInner >>^ R.NestedAlt
                          ]

parseProc :: T.Parser T.ProgTree R.ProcBody
parseProc = T.choices [ parseOptRepl "PAR" parseProc >>^ (R.Par [])
                      , T.tree (\decl (R.Par [] body) -> R.Par decl body) (S.parseChanDecls) (T.one $ parseOptRepl "PAR" parseProc >>^ (R.Par []))
                      , parseOptRepl "ALT" parseAltInner >>^ R.Alt
                      , T.simpleTree $ S.parseQuerySend
                      , T.simpleTree $ S.parseSkipCall
                      , parseCommon parseProc >>^ R.Common
                      ]

parseProcedure :: T.Parser T.ProgTree R.Procedure
parseProcedure = T.tree ($) S.parseProcHeader (T.one parseProc)

parseStatic :: T.Parser T.ProgTree R.Static
parseStatic = T.simpleTree S.parseStatic

data TopLevel = S R.Static | F R.Function | P R.Procedure

parseTopLevel :: T.Parser T.ProgTree TopLevel
parseTopLevel = T.choices [ parseStatic >>^ S
                          , parseFunction >>^ F
                          , parseProcedure >>^ P
                          ]

parseProgram :: T.Parser [T.ProgTree] R.Program
parseProgram = T.many parseTopLevel >>^
               -- Separate the 3 types of top level into a
               -- (nested) triple based on the constructor
               (foldl (\acc tl -> case tl of
                                    S s -> map1 s acc
                                    F f -> map2 f acc
                                    P p -> map3 p acc
                      ) (([],[]),[])) >>^
               (uncurry . uncurry $ R.Program)
               where
                map1 a ((as, bs), cs) = ((a:as, bs), cs)
                map2 b ((as, bs), cs) = ((as, b:bs), cs)
                map3 c ((as_and_bs), cs) = ((as_and_bs), c:cs)