{-# LANGUAGE KindSignatures, DataKinds       #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Print where

import qualified Text.PrettyPrint.GenericPretty as GPretty
import qualified Text.Show.Pretty as SPretty

import Data.Void(Void, absurd)

import qualified Types as T
import qualified RawAST as R

pretty :: (GPretty.Out a) => a -> String
pretty = GPretty.pretty

pretty2 :: (Show a) => a -> String
pretty2 = SPretty.ppShow

instance GPretty.Out T.BaseTy
instance GPretty.Out T.ChanTy
instance GPretty.Out T.VarTy
instance GPretty.Out T.StoreTy
instance GPretty.Out T.FuncTy
instance GPretty.Out T.ProcArg
instance GPretty.Out T.ProcTy
instance GPretty.Out T.CallTy

instance GPretty.Out Void where
  docPrec _ v = absurd v
  doc v = absurd v
instance GPretty.Out R.Ref
instance GPretty.Out R.Literal
instance GPretty.Out R.Binop
instance GPretty.Out R.Monop
instance GPretty.Out R.FCall
instance GPretty.Out R.Expr
instance GPretty.Out body => GPretty.Out (R.Repl body)
instance GPretty.Out R.Guard
instance GPretty.Out inj => GPretty.Out (R.CommonBody inj)
instance GPretty.Out R.VarDecl
instance GPretty.Out R.ChanDecl
instance GPretty.Out R.EAssign
instance GPretty.Out R.FAssign
instance GPretty.Out R.Valof
instance GPretty.Out R.Function
instance GPretty.Out R.InnerAlt
instance GPretty.Out R.ProcBody
instance GPretty.Out R.Procedure
instance GPretty.Out R.StaticKind
instance GPretty.Out R.Static
instance GPretty.Out R.Program
