{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE ApplicativeDo          #-}
{-# LANGUAGE DataKinds              #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs                  #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE PolyKinds              #-}
{-# LANGUAGE RankNTypes             #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TypeFamilies           #-}
{-# LANGUAGE TypeInType             #-}
{-# LANGUAGE TypeOperators          #-}
{-# LANGUAGE UndecidableInstances   #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}

module Common where

import           Data.Kind
import           Data.Void   (Void, absurd)

import qualified Expressions as E
import qualified RawAST      as R
import qualified Types       as T

data Assignment :: [T.StoreTy] -> [T.CallTy] -> Type where
    NilAssign :: Assignment stores calls
    ConsAssign :: T.SBaseTy ty ->
                  E.VarLocation stores calls ('T.Base ty) ->
                  E.Expr stores calls ty ->
                  Assignment stores calls ->
                  Assignment stores calls

deriving instance Show (Assignment stores calls)

data Vect :: T.Nat -> * -> * where
    VNil :: Vect 'T.Zero k
    VCons :: k -> Vect n k -> Vect ('T.Succ n) k


deriving instance Show k => Show (Vect n k)

vectMap :: (k -> k2) -> Vect n k -> Vect n k2
vectMap _ VNil = VNil
vectMap f (VCons x rest) = VCons (f x) (vectMap f rest)

type family VarDimension (v :: T.VarTy) :: T.Nat where
    VarDimension ('T.Base _) = 'T.Zero
    VarDimension ('T.Arr ty) = 'T.Succ (VarDimension ty)

type family ChanDimension (v :: T.ChanTy) :: T.Nat where
    ChanDimension ('T.ChanArr ty) = 'T.Succ (ChanDimension ty)
    ChanDimension _ = 'T.Zero

type family Dimension (v :: T.StoreTy) :: T.Nat where
    Dimension ('T.Var ty) = VarDimension ty
    Dimension ('T.Chan ty) = ChanDimension ty

data Common (k :: [T.StoreTy] -> [T.CallTy] -> Type) :: [T.StoreTy] -> [T.CallTy] -> Type where
    Inj :: k stores calls -> Common k stores calls
    Assign :: Assignment stores calls -> Common k stores calls
    MultiAssign :: T.ListPointer calls ('T.Func ('T.FuncTy inputs outputs)) -> -- function to call
                   T.HList (E.Expr stores calls) inputs -> -- parameters of function
                   T.HList (E.BaseVarLocation stores calls) outputs -> -- variables to assign to
                   Common k stores calls
    Stop :: Common k stores calls
    If :: [(E.Expr stores calls ('T.BoolTy), Common k stores calls)] -> Common k stores calls
    While :: E.Expr stores calls ('T.BoolTy) -> Common k stores calls -> Common k stores calls
    Seq :: [Common k stores calls] -> Common k stores calls
    ReplSeq :: E.Expr stores calls ('T.IntTy) ->
               E.Expr stores calls ('T.IntTy) ->
               Common k ('T.Var ('T.Base 'T.IntTy) ': stores) calls ->
               Common k stores calls
    DeclareVar :: T.SVarTy ty -> Vect (VarDimension ty) (E.Expr stores calls 'T.IntTy) -> Common k ('T.Var ty ': stores) calls -> Common k stores calls

type Reader raw res = forall stores calls. T.Contexts stores calls ->
                                           raw ->
                                           T.ErrorM (res stores calls)

readCommon :: forall inj inj_res stores calls.
                                     Reader inj inj_res ->
                                     T.Contexts stores calls ->
                                     R.CommonBody inj ->
                                     T.ErrorM (Common inj_res stores calls)
readCommon f c (R.Inj inj_body) = Inj <$> f c inj_body
readCommon _ c (R.Assign (Left (R.EAssign refs exprs))) =
                  Assign <$> helper refs exprs
                    where
                      helper :: [R.Ref] -> [R.Expr] -> T.ErrorM (Assignment stores calls)
                      helper [] [] = Right NilAssign
                      helper (ref : rest) (expr : rest2) =
                          case E.readLoc c ref of
                              Right (T.TyWrap (T.SBase marker) loc) ->
                                ConsAssign marker loc <$> E.readExprDispatch marker c expr
                                                      <*> helper rest rest2
                              Left err -> Left err
                      helper refs exprs = Left . T.InterpretError $ "wrong number of assignments " ++ show refs ++ " " ++ show exprs
readCommon _ c (R.Assign (Right (R.FAssign refs (R.FCall f_id params)))) =
                  case T.contextLookup (T._calls c) f_id of
                      Right (T.TyWrap (T.SFuncCall (T.SFunc inputs outputs)) f_loc) ->
                          MultiAssign f_loc <$> helper1 params inputs
                                            <*> helper2 refs outputs
                      Left err -> Left err
                    where
                      helper1 :: [R.Expr] ->
                                 T.HList T.SBaseTy tys ->
                                 T.ErrorM (T.HList (E.Expr stores calls) tys)
                      helper1 [] T.HNil = Right T.HNil
                      helper1 (e : es) (T.HCons marker rest) =
                          T.HCons <$> E.readExprDispatch marker c e
                                  <*> helper1 es rest
                      helper1 _ _ = Left . T.InterpretError $ "wrong number of function inputs  " ++ show params ++ " " ++ show f_id
                      helper2 :: [R.Ref] ->
                                 T.HList T.SBaseTy tys ->
                                 T.ErrorM (T.HList (E.BaseVarLocation stores calls) tys)
                      helper2 [] T.HNil = Right T.HNil
                      helper2 (r : rs) (T.HCons marker rest) =
                          T.HCons <$> (E.MkComp <$> E.readLocTy c (T.SBase marker) r)
                                  <*> helper2 rs rest
                      helper2 _ _ = Left . T.InterpretError $ "wrong number of function outputs  " ++ show refs ++ " " ++ show f_id
readCommon f c (R.If branches) =
                    If <$> mapM (\(branch, body) ->
                                    (,) <$> E.readExpr c branch
                                        <*> readCommon f c body
                                ) branches
readCommon f c (R.While test body) = While <$> E.readExpr c test
                                           <*> readCommon f c body
readCommon _ _ R.Stop = Right Stop
readCommon f c (R.Seq (R.VarDecl str ty exprs : decls) body) =
                  case T.liftVarTy ty of
                      T.TyWrap ty_marker _ ->
                        do arr_dims <- read_dims ty_marker exprs
                           let new_context = T.addVar str ty_marker c
                           new_body <- readCommon f new_context (R.Seq decls body)
                           return $ DeclareVar ty_marker arr_dims new_body
                  where
                    read_dims :: T.SVarTy ty -> [R.Expr] -> T.ErrorM (Vect (VarDimension ty) (E.Expr stores calls 'T.IntTy))
                    read_dims (T.SBase _) [] = Right VNil
                    read_dims (T.SArr arr_ty) (e : es) = VCons <$> E.readExpr c e <*> read_dims arr_ty es
                    read_dims ty es = Left . T.InterpretError $ "Wrong number of array dimensions " ++ show ty ++ " " ++ show es

readCommon f c (R.Seq [] (R.ListRepl body)) = Seq <$> mapM (readCommon f c) body
readCommon f c (R.Seq [] (R.IndexRepl str e1 e2 body)) =
                ReplSeq <$> E.readExpr c e1
                        <*> E.readExpr c e2
                        <*> readCommon f (T.addVar str (T.SBase T.SInt) c) body

data Const2 a b c = DConst a deriving Show

type ValofBody stores calls = Common (Const2 Void) stores calls

deriving instance Show (Common (Const2 Void) stores calls)

readValofBody :: Reader (R.CommonBody Void) ValofBody
readValofBody = readCommon (\_ -> absurd)

data ValofDecls :: [T.StoreTy] -> [T.CallTy] -> [T.VarTy] -> Type where
  NilD :: ValofDecls stores calls '[]
  ConsD :: T.SVarTy s -> Vect (VarDimension s) (E.Expr stores calls 'T.IntTy) -> ValofDecls stores calls tys -> ValofDecls stores calls (s ': tys)

data Valof :: [T.StoreTy] -> [T.CallTy] -> [T.BaseTy] -> Type where
  Valof :: ValofDecls stores calls decls ->
           ValofBody (T.Append (T.Map 'T.Var decls) stores) calls ->
           T.HList (E.Expr (T.Append (T.Map 'T.Var decls) stores) calls) results ->
           Valof stores calls results

deriving instance Show (ValofDecls stores calls decls)
deriving instance Show (Valof stores calls outs)

readValof :: forall stores calls results. T.Contexts stores calls ->
                                          T.HList T.SBaseTy results ->
                                          R.Valof ->
                                          T.ErrorM (Valof stores calls results)
readValof c res (R.Valof decls body results) = helper c NilD decls
    where
      helper :: forall ts. T.Contexts (T.Append (T.Map 'T.Var ts) stores) calls -> ValofDecls stores calls ts -> [R.VarDecl] -> T.ErrorM (Valof stores calls results)
      helper c1 decls1 [] = Valof decls1 <$> readValofBody c1 body <*> read_results res results
                             where
                               read_results :: T.HList T.SBaseTy res -> [R.Expr] -> T.ErrorM (T.HList (E.Expr (T.Append (T.Map 'T.Var ts) stores) calls) res)
                               read_results T.HNil [] = Right T.HNil
                               read_results (T.HCons ty rest) (e : es) = T.HCons <$> E.readExprDispatch ty c1 e
                                                                                 <*> read_results rest es
                               read_results tys es = Left . T.InterpretError $ "wrong number of results exprs " ++ show tys ++ " " ++ show es
      helper c1 decls1 (R.VarDecl str ty dims : rest) =
          case T.liftVarTy ty of
              T.TyWrap ty_marker _ ->
                do arr_dims <- read_dims ty_marker dims
                   let new_context = T.addVar str ty_marker c1
                   helper new_context (ConsD ty_marker arr_dims decls1) rest
          where
            read_dims :: T.SVarTy ty -> [R.Expr] -> T.ErrorM (Vect (VarDimension ty) (E.Expr stores calls 'T.IntTy))
            read_dims (T.SBase _) [] = Right VNil
            read_dims (T.SArr arr_ty) (e : es) = VCons <$> E.readExpr c e <*> read_dims arr_ty es
            read_dims ty es = Left . T.InterpretError $ "wrong number of dims " ++ show ty ++ " " ++ show es

data Function :: [T.StoreTy] -> [T.CallTy] -> T.FuncTy -> Type where
  Func :: T.SFuncTy ('T.FuncTy ins outs) ->
          Valof (T.Append (T.Map 'T.Var (T.Map 'T.Base ins)) stores) calls outs ->
          Function stores calls ('T.FuncTy ins outs)

deriving instance Show (Function stores calls ty)