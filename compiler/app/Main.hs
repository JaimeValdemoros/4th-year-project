module Main where

import System.Environment
import Data.List(intersperse)

import Parser.Parse
import Parser.Tree
import qualified Types as T
import qualified RawAST as R
import qualified Common as C
import qualified Program as Prog
import qualified UnboundedStack as U
import qualified Export as E
import qualified Print as P


main :: IO ()
main = do arg <- getArgs
          case arg of
            ("show" : file : _) -> readFile file >>= readProg >>= raw2Prog >>= (putStrLn . P.pretty2 . compile)
            ("write" : file : out_file : _) -> readFile file >>= readProg >>= raw2Prog >>= (output out_file . compile)
            _ -> error "Params did not match"

readProg :: String -> IO R.Program
readProg s = case (runParser parseProgram) . parseStructure $ s of
                Just p -> return p
                Nothing -> error "Could not parse"

raw2Prog :: R.Program -> IO Prog.Program
raw2Prog p = case Prog.readProgram p of
                 Right prog -> return prog
                 Left (T.InterpretError s) -> error s

compile :: Prog.Program -> U.StackProgram
compile = U.compileProgram

output :: String -> U.StackProgram -> IO ()
output file prog = let progs = E.convertAll prog
                   in E.write file . (E.make_labels . concat) $ progs