{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}

module RawAST where

import GHC.Generics
import           Data.Void (Void)

import qualified Types     as T

data Ref = Ref T.Ident [Expr] deriving (Show, Generic)

data Literal = UnitLit
             | BoolLit Bool
             | CharLit Char
             | IntLit Int
             | ArrLit [Literal]
             deriving (Show, Generic)


data Binop = Add | Minus | Mul | Div | Mod | And | Or | CompareEQ | CompareGT | CompareGTE deriving (Show, Generic)


data Monop = Neg | Not deriving (Show, Generic)


data FCall = FCall T.Ident [Expr] deriving (Show, Generic)

data Expr = Unit
          | Lookup Ref
          | CallFunction FCall
          | Lit Literal
          | Binop Binop Expr Expr
          | Monop Monop Expr
          | ExprIf Expr Expr Expr
          | Length Ref
          deriving (Show, Generic)

data VarDecl  = VarDecl T.Ident T.VarTy [Expr] deriving (Show, Generic)
data ChanDecl = ChanDecl T.Ident T.ChanTy [Expr] deriving (Show, Generic)

data Repl body = IndexRepl T.Ident Expr Expr body
               | ListRepl [body]
               deriving (Show, Generic)

data EAssign = EAssign [Ref] [Expr] deriving (Show, Generic) -- length _exprs == length _vars
data FAssign = FAssign [Ref] FCall deriving (Show, Generic) -- length _vars = length (result _fun)
type Assign = Either EAssign FAssign

data Guard = InputGuard Ref T.Ident | TimGuard Expr | SkipGuard deriving (Show, Generic)

-- The Common datatype describes the common features of Functions and Procedures
-- 'inj' is a datatype allowed to be injected into the tree structure
data CommonBody inj = Inj inj
                    | Assign Assign
                    | If [(Expr, CommonBody inj)]
                    | While Expr (CommonBody inj)
                    | Stop
                    | Seq [VarDecl] (Repl (CommonBody inj))
                     deriving (Show, Generic)

data Valof = Valof [VarDecl] (CommonBody Void) [Expr] deriving (Show, Generic)

type FunctionParam = (T.Ident, T.BaseTy)

-- <T1, T2, ..> FUNCTION <name> (<param1, ...>)
--   <decls>
--   SEQ
--     <body>
--   RESULT <expr1, expr2, ...>
data Function = Function { _fResultType :: [T.BaseTy]
                         , _fName       :: String
                         , _fParams     :: [FunctionParam]
                         , _fBody       :: Valof
                         }
                         deriving (Show, Generic)

-- PROC <name> (<param1, ...>)
--   <body>
data InnerAlt = AltBranch Expr Guard ProcBody | NestedAlt Alt deriving (Show, Generic)
type Alt = Repl InnerAlt

data ProcBody = Skip
              | Common (CommonBody ProcBody)
              | Key Ref
              | Screen Expr
              | Query Ref Ref -- <chan> ? <var>
              | Send Ref Expr -- <chan> ! <expr>
              | Par [ChanDecl] (Repl ProcBody)
              | Alt Alt
              | Call T.Ident [Expr]
              deriving (Show, Generic)

data Procedure = Procedure { _pName   :: T.Ident
                           , _pParams :: [(T.Ident, T.ProcArg)]
                           , _pBody   :: ProcBody
                           } deriving (Show, Generic)

-- Static declarations are either channels or immutable values
data StaticKind = StaticChan [Int] T.BaseTy | StaticVal T.VarTy Literal deriving (Show, Generic)
data Static = Static { _sName :: T.Ident, _sKind :: StaticKind } deriving (Show, Generic)

data Program = Program { _statics    :: [Static]
                       , _functions  :: [Function]
                       , _procedures :: [Procedure]
                       } deriving (Show, Generic)