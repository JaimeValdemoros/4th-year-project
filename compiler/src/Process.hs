{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeInType            #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving, FlexibleInstances, TypeFamilyDependencies #-}

module Process where

import           Data.Kind
import qualified Common      as C
import qualified Expressions as E
import qualified RawAST      as R
import qualified Types       as T

data AltBranch stores calls where
    SkipGuard :: Process stores calls -> AltBranch stores calls
    ChanGuard :: E.ChanLocation stores calls ty ->
                 T.SCast ty ('T.ChanInput ty2) ->
                 T.SBaseTy ty2 ->
                 Process ('T.Var ('T.Base ty2) ': stores) calls ->
                 AltBranch stores calls
    TimeGuard :: E.Expr stores calls 'T.IntTy ->
                 Process stores calls ->
                 AltBranch stores calls

deriving instance Show (AltBranch stores calls)

data ProcParam :: [T.StoreTy] -> [T.CallTy] -> T.ProcArg -> Type where
    ExprParam :: E.Expr stores calls ty ->
                 ProcParam stores calls ('T.ProcConst ty)
    VarParam ::  E.VarLocation stores calls ty ->
                 ProcParam stores calls ('T.ProcVar ty)
    ChanParam :: E.ChanLocation stores calls ty ->
                 T.SCast ty ty2 ->
                 ProcParam stores calls ('T.ProcChan ty2)

deriving instance Show (ProcParam stores calls arg)

data Alt :: [T.StoreTy] -> [T.CallTy] -> Type where
    SeqAlt :: [InnerAlt stores calls] -> Alt stores calls
    ReplAlt :: E.Expr stores calls 'T.IntTy -> E.Expr stores calls 'T.IntTy ->
               InnerAlt ('T.Var ('T.Base 'T.IntTy) ': stores) calls ->
               Alt stores calls

data InnerAlt :: [T.StoreTy] -> [T.CallTy] -> Type where
    AltBranch :: E.Expr stores calls 'T.BoolTy ->
                AltBranch stores calls ->
                InnerAlt stores calls
    NestedAlt :: Alt stores calls -> InnerAlt stores calls

deriving instance Show (InnerAlt stores calls)
deriving instance Show (Alt stores calls)

data Process :: [T.StoreTy] -> [T.CallTy] -> Type where
    Common :: C.Common Process stores calls -> Process stores calls
    CallProc :: T.ListPointer calls ('T.Proc ('T.ProcTy inputs)) ->
                T.HList (ProcParam stores calls) inputs ->
                Process stores calls
    Keyboard :: E.VarLocation stores calls ('T.Base 'T.CharTy) ->
                Process stores calls
    Screen :: E.Expr stores calls 'T.CharTy ->
              Process stores calls
    IntScreen :: E.Expr stores calls 'T.IntTy ->
                 Process stores calls
    Input :: E.ChanLocation stores calls ty ->
             T.SCast ty ('T.ChanInput ty2) ->
             E.VarLocation stores calls ('T.Base ty2) ->
             Process stores calls
    Output :: E.ChanLocation stores calls ty ->
              T.SCast ty ('T.ChanOutput ty2) ->
              E.Expr stores calls ty2 ->
              Process stores calls
    Skip :: Process stores calls
    Par :: [Process stores calls] -> Process stores calls
    ReplPar :: E.Expr stores calls ('T.IntTy) ->
               E.Expr stores calls ('T.IntTy) ->
               Process ('T.Var ('T.Base 'T.IntTy) ': stores) calls ->
               Process stores calls
    Alt :: Alt stores calls -> Process stores calls
    DeclareChan :: T.SChanTy ty -> C.Vect (C.ChanDimension ty) (E.Expr stores calls 'T.IntTy) -> Process ('T.Chan ty ': stores) calls -> Process stores calls

deriving instance Show (T.HList (ProcParam stores calls) inputs)
deriving instance Show (C.Common Process stores calls)
deriving instance Show (Process stores calls)

readGuard :: T.Contexts stores calls -> R.Guard -> R.ProcBody -> T.ErrorM (AltBranch stores calls)
readGuard c R.SkipGuard body = SkipGuard <$> readProc c body
readGuard c (R.TimGuard e) body = TimeGuard <$> E.readExpr c e <*> readProc c body
readGuard c (R.InputGuard ref ident) body =
              case E.readChanLoc c ref of
                  Right (T.TyWrap c_marker c_loc) ->
                      case c_marker of
                          T.SChanInput ty ->
                              ChanGuard c_loc T.SRefl ty
                                        <$> readProc (T.addVar ident (T.SBase ty) c) body
                          T.SChanBoth ty ->
                              ChanGuard c_loc T.SBothToLeft ty
                                        <$> readProc (T.addVar ident (T.SBase ty) c) body
                          ty -> Left . T.InterpretError $ "wrong type guard " ++ show ty
                  Left err -> Left err


readProc :: forall stores calls. T.Contexts stores calls ->
                                 R.ProcBody ->
                                 T.ErrorM (Process stores calls)
readProc c (R.Common body) = Common <$> C.readCommon readProc c body
readProc c (R.Call p_id params) =
              case T.contextLookup (T._calls c) p_id of
                  Right (T.TyWrap (T.SProcCall (T.SProc inputs_ty)) p_loc) ->
                          CallProc p_loc <$> helper params inputs_ty
                  Left err -> Left err
                where
                  helper :: [R.Expr] ->
                            T.HList T.SProcArg tys ->
                            T.ErrorM (T.HList (ProcParam stores calls) tys)
                  helper [] T.HNil = Right T.HNil
                  helper (R.Lookup ref : exprs) (T.HCons (T.SVarArg ty) rest) =
                      T.HCons <$> fmap VarParam (E.readLocTy c ty ref)
                              <*> helper exprs rest
                  helper (R.Lookup ref : exprs) (T.HCons (T.SChanArg ty) rest) =
                    case E.readChanLoc c ref of
                      Right (T.TyWrap chan_type loc) ->
                        T.HCons <$> (ChanParam loc <$> (T.liftE (T.canCast chan_type ty) $ "cast type " ++ show chan_type ++ " " ++ show ty))
                                <*> helper exprs rest
                      Left err -> Left err
                  helper (e : exprs) (T.HCons (T.SConstArg ty) rest) =
                        T.HCons <$> (ExprParam <$> E.readExprDispatch ty c e)
                                <*> helper exprs rest
                  helper es tys = Left . T.InterpretError $ "mismatched parameter types " ++ show es ++ " " ++ show tys
readProc _ R.Skip = Right Skip
readProc c (R.Screen e) = case (Screen <$> E.readExprDispatch T.SChar c e) of
                            Right x -> Right x
                            Left (T.InterpretError err) -> case (IntScreen <$> E.readExprDispatch T.SInt c e) of
                                          Right y -> Right y
                                          Left (T.InterpretError err2) -> Left . T.InterpretError $ "(" ++ err ++ " , " ++ err2 ++ ")"
readProc c (R.Key ref) = case E.readLocTy c (T.SBase T.SChar) ref of
                           Right loc ->
                               return $ Keyboard loc
                           Left err -> Left err
readProc c (R.Query chan_label var_label) =
              do chan_loc <- E.readChanLoc c chan_label
                 var_loc <- E.readLoc c var_label
                 case (chan_loc, var_loc) of
                    (T.TyWrap c_marker c_loc, T.TyWrap (T.SBase marker2) v_loc) ->
                        Input c_loc <$> (T.liftE (T.canCast c_marker (T.SChanInput marker2)) $ "cast " ++ show c_marker ++ " " ++ show marker2)
                                    <*> pure v_loc
                    _ -> Left . T.InterpretError $ "writing to a non-base type " ++ show (R.Query chan_label var_label)
readProc c (R.Send chan_label expr) =
              case E.readChanLoc c chan_label of
                  Right (T.TyWrap c_marker c_loc) ->
                      case c_marker of
                          T.SChanBoth ty ->
                              Output c_loc T.SBothToRight <$> E.readExprDispatch ty c expr
                          T.SChanOutput ty ->
                              Output c_loc T.SRefl <$> E.readExprDispatch ty c expr
                          ty -> Left . T.InterpretError $ "wrong type send " ++ show (R.Send chan_label expr)
                  Left err -> Left err
readProc c (R.Par (R.ChanDecl str ty exprs : decls) body) =
              case T.liftChanTy ty of
                  T.TyWrap ty_marker _ ->
                    do arr_dims <- read_dims ty_marker exprs
                       let new_context = T.addChan str ty_marker c
                       read_body <- readProc new_context (R.Par decls body)
                       return $ DeclareChan ty_marker arr_dims read_body
              where
                read_dims :: T.SChanTy ty -> [R.Expr] -> T.ErrorM (C.Vect (C.ChanDimension ty) (E.Expr stores calls 'T.IntTy))
                read_dims (T.SChanArr arr_ty) (e : es) = C.VCons <$> E.readExpr c e <*> read_dims arr_ty es
                read_dims (T.SChanBoth _) [] = Right C.VNil
                read_dims ty es = Left . T.InterpretError $ "mismatched types chandecl " ++ show ty ++ " " ++ show es

readProc c (R.Par [] (R.ListRepl body)) = Par <$> mapM (readProc c) body
readProc c (R.Par [] (R.IndexRepl str e1 e2 body)) =
              ReplPar <$> E.readExpr c e1
                      <*> E.readExpr c e2
                      <*> readProc (T.addVar str (T.SBase T.SInt) c) body

readProc c (R.Alt alt) = Alt <$> readAlt c alt

readAlt :: forall stores calls. T.Contexts stores calls ->
                                R.Alt ->
                                T.ErrorM (Alt stores calls)
readAlt c (R.ListRepl inners) = SeqAlt <$> mapM (readAltInner c) inners
readAlt c (R.IndexRepl str e1 e2 inner) = ReplAlt <$> E.readExpr c e1 <*> E.readExpr c e2
                                                  <*> readAltInner (T.addVar str (T.SBase T.SInt) c) inner

readAltInner :: forall stores calls. T.Contexts stores calls ->
                                     R.InnerAlt ->
                                     T.ErrorM (InnerAlt stores calls)
readAltInner c (R.AltBranch test guard body) = AltBranch <$> E.readExpr c test
                                                         <*> readGuard c guard body
readAltInner c (R.NestedAlt a) = NestedAlt <$> readAlt c a

type family Args2Store (args :: [T.ProcArg]) = (res :: [T.StoreTy]) | res -> args where
  Args2Store '[] = '[]
  Args2Store ('T.ProcConst ty ': rest) = 'T.Var ('T.Base ty) ': Args2Store rest
  Args2Store ('T.ProcVar ('T.Base ty) ': rest) = 'T.Ref ty ': Args2Store rest
  Args2Store ('T.ProcVar ('T.Arr ty) ': rest) = 'T.Var ('T.Arr ty) ': Args2Store rest
  Args2Store ('T.ProcChan ty ': rest) = 'T.Chan ty ': Args2Store rest

data Procedure :: [T.StoreTy] -> [T.CallTy] -> [T.ProcArg] -> Type where
  Proc :: T.SProcTy ('T.ProcTy tys) -> Process (T.Append (Args2Store tys) stores) calls -> Procedure stores calls tys

deriving instance Show (Procedure stores calls args)