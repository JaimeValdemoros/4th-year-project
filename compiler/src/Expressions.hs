{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE InstanceSigs        #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -fwarn-incomplete-patterns #-}

module Expressions where

import qualified RawAST         as R
import qualified Types          as T

import           Data.Kind
import           Data.Semigroup ((<>))

data Literal :: T.VarTy -> Type where
 UnitLit :: Literal ('T.Base 'T.UnitTy)
 BoolLit :: Bool -> Literal ('T.Base 'T.BoolTy)
 CharLit :: Char -> Literal ('T.Base 'T.CharTy)
 IntLit :: Int -> Literal ('T.Base 'T.IntTy)
 ArrayLit :: [Literal a] -> Literal ('T.Arr a)

deriving instance Show (Literal a)
deriving instance Eq (Literal a)
--
--data Monop :: T.BaseTy -> T.BaseTy -> Type where
--  Neg :: Monop 'T.IntTy 'T.IntTy
--  Not :: Monop 'T.BoolTy 'T.BoolTy
--
--data Binop :: T.BaseTy -> T.BaseTy -> Type where


-- A value of type (Expr ctx a), where ctx is a list of occam types, is an expression that
-- may have free variables indexed by ctx and evaluates to a value of type a
data Expr :: [T.StoreTy] -> [T.CallTy] -> T.BaseTy -> Type where
  Unit :: Expr stores calls 'T.UnitTy
--  Monop :: Monop a b -> Expr a -> Expr b
--  Binop :: Binop a b c -> Expr stores calls a -> Expr stores calls b -> Expr stores calls c

  Add :: Expr stores calls 'T.IntTy -> Expr stores calls 'T.IntTy -> Expr stores calls 'T.IntTy
  Mul :: Expr stores calls 'T.IntTy -> Expr stores calls 'T.IntTy -> Expr stores calls 'T.IntTy
  Div :: Expr stores calls 'T.IntTy -> Expr stores calls 'T.IntTy -> Expr stores calls 'T.IntTy
  Mod :: Expr stores calls 'T.IntTy -> Expr stores calls 'T.IntTy -> Expr stores calls 'T.IntTy
  Neg :: Expr stores calls 'T.IntTy -> Expr stores calls 'T.IntTy
  And :: [Expr stores calls 'T.BoolTy] -> Expr stores calls 'T.BoolTy
  Or :: [Expr stores calls 'T.BoolTy] -> Expr stores calls 'T.BoolTy
  Not :: Expr stores calls 'T.BoolTy -> Expr stores calls 'T.BoolTy
  CompareEQ :: Expr stores calls a ->
               Expr stores calls a ->
               Expr stores calls 'T.BoolTy
  CompareGT :: Expr stores calls 'T.IntTy ->
               Expr stores calls 'T.IntTy ->
               Expr stores calls 'T.BoolTy
  CompareGE :: Expr stores calls 'T.IntTy ->
               Expr stores calls 'T.IntTy ->
               Expr stores calls 'T.BoolTy
  Literal :: Literal ('T.Base ty) -> Expr stores calls ty
  Variable :: VarLocation stores calls ('T.Base ty) -> Expr stores calls ty
  Length :: VarLocation stores calls ('T.Arr ty) -> Expr stores calls 'T.IntTy
  ChanLength :: ChanLocation stores calls ('T.ChanArr ty) -> Expr stores calls 'T.IntTy
  If :: Expr stores calls 'T.BoolTy ->
        Expr stores calls a ->
        Expr stores calls a ->
        Expr stores calls a
  FCall :: T.ListPointer calls ('T.Func ('T.FuncTy inputs '[ty])) ->
           T.HList (Expr stores calls) inputs ->
           Expr stores calls ty

deriving instance Show (T.HList (Expr stores calls) inputs)
deriving instance Show (Expr stores calls a)

class ReadExpr (ty :: T.BaseTy) where
  readExpr :: T.Contexts stores calls -> R.Expr -> T.ErrorM (Expr stores calls ty)

readExprDispatch :: T.SBaseTy ty ->
                    T.Contexts stores calls ->
                    R.Expr ->
                    T.ErrorM (Expr stores calls ty)
readExprDispatch T.SUnit = readExpr
readExprDispatch T.SBool = readExpr
readExprDispatch T.SChar = readExpr
readExprDispatch T.SInt = readExpr

--deriving instance Show (T.HList T.SBaseTy tys)

readLiteral :: T.SVarTy ty -> R.Literal -> T.ErrorM (Literal ty)
readLiteral (T.SArr ty) (R.ArrLit list) = fmap ArrayLit . mapM (readLiteral ty) $ list
readLiteral (T.SBase T.SUnit) R.UnitLit = Right UnitLit
readLiteral (T.SBase T.SBool) (R.BoolLit b) = Right $ BoolLit b
readLiteral (T.SBase T.SInt) (R.IntLit i) = Right $ IntLit i
readLiteral ty lit = Left . T.InterpretError $ "couldn't interpret" ++ show lit ++ " as " ++ show ty

instance ReadExpr 'T.UnitTy where
  readExpr :: forall stores calls. T.Contexts stores calls ->
                                   R.Expr ->
                                   T.ErrorM (Expr stores calls 'T.UnitTy)
  readExpr _ (R.Lit R.UnitLit) = Right Unit
  readExpr c (R.Lookup ref) = Variable <$> readLocTy c (T.SBase T.SUnit) ref
  readExpr c (R.ExprIf e1 e2 e3) = If <$> readExpr c e1 <*> readExpr c e2 <*> readExpr c e3
  readExpr c (R.CallFunction (R.FCall ident exprs)) =
      case T.contextLookup (T._calls c) ident of
          Right (T.TyWrap (T.SFuncCall (T.SFunc inputs (T.HCons T.SUnit T.HNil))) loc) ->
              FCall loc <$> helper exprs inputs
          Left err -> Left err
          _ -> Left . T.InterpretError $ "couldnt find " ++ show ident
        where
          helper :: [R.Expr] -> T.HList T.SBaseTy tys -> T.ErrorM (T.HList (Expr stores calls) tys)
          helper [] T.HNil = Right T.HNil
          helper (e : es) (T.HCons marker rest) = T.HCons <$> readExprDispatch marker c e
                                                          <*> helper es rest
          helper es tys = Left . T.InterpretError $ "wrong number of arguments " ++ show es ++ " " ++ show tys
  readExpr _ expr =  Left . T.InterpretError $ "not a unit " ++ show expr

eqHelper :: forall stores calls.
          T.Contexts stores calls ->
          R.Expr ->
          R.Expr ->
          T.ErrorM (Expr stores calls 'T.BoolTy)
eqHelper c e1 e2 = (CompareEQ <$> (readExpr c e1 :: T.ErrorM (Expr stores calls 'T.CharTy))
                              <*> readExpr c e2)
                   <>
                   (CompareEQ <$> (readExpr c e1 :: T.ErrorM (Expr stores calls 'T.IntTy))
                              <*> readExpr c e2)

instance ReadExpr 'T.BoolTy where
  readExpr _ (R.Lit (R.BoolLit b)) = Right . Literal . BoolLit $ b
  readExpr c (R.Lookup ref) = Variable <$> readLocTy c (T.SBase T.SBool) ref
  readExpr c (R.Monop R.Not e) = Not <$> readExpr c e
  readExpr c (R.Binop R.And e1 e2) = And <$> mapM (readExpr c) [e1, e2]
  readExpr c (R.Binop R.Or e1 e2) = Or <$> mapM (readExpr c) [e1, e2]
  readExpr c (R.Binop R.CompareEQ e1 e2) = eqHelper c e1 e2
  readExpr c (R.Binop R.CompareGT e1 e2) = CompareGT <$> readExpr c e1
                                                     <*> readExpr c e2
  readExpr c (R.Binop R.CompareGTE e1 e2) = CompareGE <$> readExpr c e1
                                                      <*> readExpr c e2
  readExpr c (R.ExprIf e1 e2 e3) = If <$> readExpr c e1
                                      <*> readExpr c e2
                                      <*> readExpr c e3
  readExpr _ expr = Left . T.InterpretError $ "not a bool " ++ show expr

instance ReadExpr 'T.CharTy where
  readExpr _ (R.Lit (R.CharLit c)) = Right . Literal . CharLit $ c
  readExpr c (R.Lookup ref) = Variable <$> readLocTy c (T.SBase T.SChar) ref
  readExpr c (R.ExprIf e1 e2 e3) = If <$> readExpr c e1
                                      <*> readExpr c e2
                                      <*> readExpr c e3
  readExpr _ expr =  Left . T.InterpretError $ "not a char " ++ show expr

instance ReadExpr 'T.IntTy where
  readExpr _ (R.Lit (R.IntLit c)) = Right . Literal . IntLit $ c
  readExpr c (R.Lookup ref) = Variable <$> readLocTy c (T.SBase T.SInt) ref
  readExpr c (R.Monop R.Neg e) = Neg <$> readExpr c e
  readExpr c (R.Binop R.Add e1 e2) = Add <$> readExpr c e1
                                         <*> readExpr c e2
  readExpr c (R.Binop R.Minus e1 e2) = readExpr c (R.Binop R.Add e1 (R.Monop R.Neg e2))
  readExpr c (R.ExprIf e1 e2 e3) = If <$> readExpr c e1
                                      <*> readExpr c e2
                                      <*> readExpr c e3
  readExpr _ expr = Left . T.InterpretError $ "not an int " ++ show expr

-----------------------------------------------------------------
------------------------------------------------------------------
------------------------------------------------------------------
------------------------------------------------------------------
------------------------------------------------------------------
------------------------------------------------------------------

data Location (wrap :: k -> T.StoreTy) (arr :: k -> k) :: [T.StoreTy] -> [T.CallTy] -> k -> Type where
  Var :: T.ListPointer stores (wrap ty) -> Location wrap arr stores calls ty
  Index :: Location wrap arr stores calls (arr ty) ->
           Expr stores calls 'T.IntTy ->
           Location wrap arr stores calls ty


deriving instance Show (Location arr stores calls tys ty)

type VarLocation = Location 'T.Var 'T.Arr
type ChanLocation = Location 'T.Chan 'T.ChanArr

data Compose (f1 :: k2 -> k3) (f2 :: k1 -> k2) :: k1 -> * where
    MkComp :: f1 (f2 ty) -> Compose f1 f2 ty

deriving instance Show (f (g t)) => Show (Compose f g t)

type BaseVarLocation stores calls = Compose (VarLocation stores calls) 'T.Base

deriving instance Show (T.HList (BaseVarLocation stores calls) outputs)

readLoc :: forall stores calls. T.Contexts stores calls ->
                                R.Ref ->
                                T.ErrorM (T.VarTyWrapper (VarLocation stores calls))
readLoc c (R.Ref i es) =
              case T.contextLookup (T._stores c) i of
                  Right (T.TyWrap (T.SVarStore ty) pos) ->
                      helper es (T.TyWrap ty (Var pos))
                  Left err -> Left err
                  _ -> Left (T.InterpretError $ "wrong type " ++ show i)
                where
                  helper :: [R.Expr] ->
                            T.VarTyWrapper (VarLocation stores calls) ->
                            T.ErrorM (T.VarTyWrapper (VarLocation stores calls))
                  helper [] loc = Right loc
                  helper (ex : exprs) (T.TyWrap (T.SArr ty) loc) =
                      readExprDispatch T.SInt c ex >>= (helper exprs . T.TyWrap ty . Index loc)
                  helper _ _ = Left . T.InterpretError $ "wrong number of indexes " ++ show i

readLocTy :: T.Contexts stores calls -> T.SVarTy ty -> R.Ref -> T.ErrorM (VarLocation stores calls ty)
readLocTy c ty_marker ref = do T.TyWrap marker loc <- readLoc c ref
                               case T.decVarEq marker ty_marker of
                                 Just T.Refl -> return loc
                                 Nothing -> Left . T.InterpretError $ "Couldnt match types " ++ show marker ++ " " ++ show ty_marker

readChanLoc :: forall stores calls. T.Contexts stores calls ->
                                    R.Ref ->
                                    T.ErrorM (T.ChanTyWrapper (ChanLocation stores calls))
readChanLoc c (R.Ref i es) =
              case T.contextLookup (T._stores c) i of
                  Right (T.TyWrap (T.SChanStore ty) pos) -> helper es (T.TyWrap ty (Var pos))
                  Left err -> Left err
                  _ -> Left . T.InterpretError $ "couldnt find identifier " ++ show i
                where
                  helper :: [R.Expr] ->
                            T.ChanTyWrapper (ChanLocation stores calls) ->
                            T.ErrorM (T.ChanTyWrapper (ChanLocation stores calls))
                  helper [] loc = Right loc
                  helper (ex : exprs) (T.TyWrap (T.SChanArr ty) loc) =
                       readExprDispatch T.SInt c ex >>= (helper exprs . T.TyWrap ty . Index loc)
                  helper _ _ = Left . T.InterpretError $ "wrong number of parameters " ++ show i ++ " " ++ show es

readChanLocTy :: T.Contexts stores calls ->
                 T.SChanTy ty ->
                 R.Ref ->
                 T.ErrorM (ChanLocation stores calls ty)
readChanLocTy c ty_marker ref = do T.TyWrap marker loc <- readChanLoc c ref
                                   case T.decChanEq marker ty_marker of
                                      Just T.Refl -> return loc
                                      Nothing -> Left . T.InterpretError $ "couldnt match types " ++ show marker ++ " " ++ show ty_marker
