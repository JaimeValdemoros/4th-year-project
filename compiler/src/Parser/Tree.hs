module Parser.Tree where

import           Control.Arrow
import           Control.Monad (liftM2)
import qualified Data.Tree     as Tree

import           Control.Arrow (first, (>>>))
import           Data.Char     (isSpace)

import qualified Parser.String as S

rootLabel :: ProgTree -> String
rootLabel = Tree.rootLabel

subForest :: ProgTree -> [ProgTree]
subForest = Tree.subForest

-- Detect comments and remove them from a string. A comment
-- begins with two dashes ('--') and continues until the end
-- of the string
stripComment :: String -> String
stripComment ('-' : '-' : _) = []
stripComment (a : s) = a : stripComment s
stripComment [] = []

-- remove and count the amount of whitespace at the beginning
-- of a string
indentation :: String -> (Int, String)
indentation = span isSpace >>> first length

-- Take a list of values paired with indentations and build a
-- forest of trees, where the children of a node are the values
-- with greater indentation
makeTrees :: [(Int, String)] -> [ProgTree]
makeTrees [] = []
makeTrees ((n,s) : xs) =
    -- we take greatest prefix of xs that has indentation strictly
    -- greater than the line we're looking at to become the children
    let (sub, rest) = span ((> n) . fst) xs
    in (Tree.Node s (makeTrees sub)) : (makeTrees rest)

-- Take a string, split it into lines and remove comments, then form
-- a tree based on the indentation of each line
parseStructure :: String -> [ProgTree]
parseStructure = lines >>> -- [String]
                  map stripComment >>> -- remove trailing comments
                  filter (not . all isSpace) >>> -- remove blank lines
                  map indentation >>>  -- [(Int, String)]
                  makeTrees

type ProgTree = Tree.Tree String

type Parser a b = Kleisli Maybe a b -- Parser (a -> Maybe b)

type TreeParser a = Parser ProgTree a

runParser :: Parser a b -> a -> Maybe b
runParser = runKleisli

mkParser :: (a -> Maybe b) -> Parser a b
mkParser = Kleisli

stringParser :: S.Parser a -> Parser String a
stringParser p = mkParser $ \s -> case S.parse p s of
                                    Left _ -> Nothing
                                    Right x -> Just x

parseFail :: Parser a b
parseFail = mkParser $ const Nothing

test :: (a -> Bool) -> Parser a a
test p = mkParser $ \x -> if p x then Just x else Nothing

choice :: Parser a b -> Parser a b -> Parser a b
choice p1 p2 = mkParser $ \x -> case runParser p1 x of
                                  Just y -> Just y
                                  Nothing -> runParser p2 x

choices :: [Parser a b] -> Parser a b
choices = foldr choice parseFail

-- Takes a parser for the the root and a parser for the leaves,
-- applies them to the root and leaves of the tree then combines
-- them with the combining function.
tree :: (a -> b -> c) ->
        S.Parser a ->
        Parser [ProgTree] b ->
        Parser ProgTree c
tree combine p1 p2 = arr Tree.rootLabel &&& arr Tree.subForest >>>
                     (stringParser p1) *** p2 >>>
                     arr (uncurry combine)

-- A parser for the special case of trees with no leaves.
simpleTree :: S.Parser a -> Parser ProgTree a
simpleTree p = tree (\x _ -> x) p (test null)

-- A parser for non-empty lists
uncons :: Parser [a] (a, [a])
uncons = mkParser f
          where f [] = Nothing
                f (x:xs) = Just (x,xs)

-- Matches a parser for x only if the input has shape [x]
one :: Parser a b -> Parser [a] b
one p = uncons >>> p *** (test null) >>> arr fst

-- map the parser over a list, allowing empty lists
many :: Parser a b -> Parser [a] [b]
many p = mkParser $ sequence . map (runParser p)

-- map the parser over a list, disallowing empty lists
many1 :: Parser a b -> Parser [a] [b]
many1 p = test (not . null) >>> many p

forestCons :: Parser a b -> Parser [a] c -> Parser [a] (b,c)
forestCons p1 p2 = uncons >>> p1 *** p2

-- specification : the following function should be equivalent
-- to
--     arr reverse >>>
--     uncons >>>
--     second reverse >>>
--     arr (\x y -> y x) >>>
--     p1 *** p2
forestSnoc :: Parser [a] b -> Parser a c -> Parser [a] (b,c)
forestSnoc p1 p2 = mkParser f
                      where
                        f [] = Nothing
                        f xs = let n = length xs in
                                   liftM2 (,) (runParser p1 $ take (n-1) xs)
                                              (runParser p2 $ last xs)
