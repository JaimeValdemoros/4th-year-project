{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE StandaloneDeriving, TypeFamilyDependencies #-}

module UnboundedStack where

-- A datatype representing operations on an unbounded stack, together with a translator from
-- expressions (Expressions.hs) to code operating on stacks

import           Data.Kind   (Type)
import Data.Void(absurd)

import qualified Common      as C
import qualified Expressions as E
import qualified Process   as P
import qualified Types       as T
import qualified Program as Prog

data StackEntry where
  Ref :: T.StoreTy -> StackEntry
  Val :: T.BaseTy -> StackEntry

type family VarBase (v :: T.VarTy) :: T.BaseTy where
  VarBase ('T.Base ty) = ty
  VarBase ('T.Arr ty) = VarBase ty

data Finite :: T.Nat -> Type where
  FZ :: Finite n
  FS :: Finite n -> Finite ('T.Succ n)

data WorkerState = Ready | Alt [StackEntry] | AltIndexed | Par | Done

-- ICFP 2012 Monday keynote. Conor McBride: Agda-curious? https://www.youtube.com/watch?v=XGyJ519RY6Y
data StackCode :: [T.StoreTy] -> [T.CallTy] -> [StackEntry] -> [StackEntry] -> WorkerState -> WorkerState -> Type where
  CNil      :: StackCode stores calls tys tys state state
  CSwap     :: StackCode stores calls (a ': b ': rest) (b ': a ': rest) state state
  CDup      :: StackCode stores calls (a ': rest) (a ': a ': rest) state state
  (:.)      :: StackCode stores calls a b state1 state2 -> StackCode stores calls b c state2 state3 -> StackCode stores calls a c state1 state3
  CInc :: StackCode stores calls ('Ref ('T.Var ('T.Base 'T.IntTy)) ': ts) ts state state
  CDec :: StackCode stores calls ('Ref ('T.Var ('T.Base 'T.IntTy)) ': ts) ts state state
  CPlus :: StackCode  stores calls ('Val 'T.IntTy ': 'Val 'T.IntTy ': ts) ('Val 'T.IntTy ': ts) state state
  CMul :: StackCode  stores calls ('Val 'T.IntTy ': 'Val 'T.IntTy ': ts) ('Val 'T.IntTy ': ts) state state
  CDiv :: StackCode  stores calls ('Val 'T.IntTy ': 'Val 'T.IntTy ': ts) ('Val 'T.IntTy ': ts) state state
  CMod :: StackCode  stores calls ('Val 'T.IntTy ': 'Val 'T.IntTy ': ts) ('Val 'T.IntTy ': ts) state state
  CNeg      :: StackCode stores calls ('Val 'T.IntTy ': ts) ('Val 'T.IntTy ': ts) state state
  CEq       :: StackCode stores calls ('Val t ': 'Val t ': ts) ('Val 'T.BoolTy ': ts) state state
  CAnd :: StackCode stores calls ('Val 'T.BoolTy ': 'Val 'T.BoolTy ': ts) ('Val 'T.BoolTy ': ts) state state
  COr :: StackCode stores calls ('Val 'T.BoolTy ': 'Val 'T.BoolTy ': ts) ('Val 'T.BoolTy ': ts) state state
  CNot      :: StackCode stores calls ('Val 'T.BoolTy ': ts) ('Val 'T.BoolTy ': ts) state state
  CCompGT   :: StackCode stores calls ('Val 'T.IntTy ': 'Val 'T.IntTy ': ts) ('Val 'T.BoolTy ': ts) state state
  CLit      :: E.Literal ('T.Base ty) -> StackCode stores calls ts ('Val ty ': ts) state state
  CIf       :: StackCode stores calls t1 t2 state state -> StackCode stores calls t1 t2 state state -> StackCode stores calls ('Val 'T.BoolTy ': t1) t2 state state
  CLookup   :: StackCode stores calls ('Ref ('T.Var ('T.Base ty)) ': ts) ('Val ty ': ts) state state
  CStore    :: StackCode stores calls ('Ref ('T.Var ('T.Base ty)) ': 'Val ty ': ts) ts state state
  CIndexV   :: StackCode stores calls ('Val 'T.IntTy ': 'Ref ('T.Var ('T.Arr ty)) ': tys)
                                      (                 'Ref ('T.Var         ty)  ': tys) state state
  CIndexC   :: StackCode stores calls ('Val 'T.IntTy ': 'Ref ('T.Chan ('T.ChanArr ty)) ': tys)
                                      (                 'Ref ('T.Chan             ty)  ': tys) state state
  CQuery    :: T.SCast ch ('T.ChanInput ty) -> StackCode stores calls ('Ref ('T.Chan ch) ': tys) ('Val ty ': tys) state state
  CSend     :: T.SCast ch ('T.ChanOutput ty) -> StackCode stores calls ('Ref ('T.Chan ch) ': 'Val ty ': tys) tys state state

  CKeyboard :: StackCode stores calls tys ('Val 'T.CharTy ': tys) state state
  CScreen :: StackCode stores calls ('Val 'T.CharTy ': tys) tys state state
  CIntScreen :: StackCode stores calls ('Val 'T.IntTy ': tys) tys state state

  CVar :: T.ListPointer stores ty -> StackCode stores calls tys ('Ref ty  ': T.Append (T.Repeat ('Val 'T.IntTy) (C.Dimension ty)) tys) state state

  CArrElemSize :: T.ListPointer stores ('T.Var ('T.Arr ty)) -> Finite (C.VarDimension ('T.Arr ty)) -> StackCode stores calls tys ('Val 'T.IntTy ': tys) state state
  CChanArrElemSize :: T.ListPointer stores ('T.Chan ('T.ChanArr ty)) -> Finite (C.ChanDimension ('T.ChanArr ty)) -> StackCode stores calls tys ('Val 'T.IntTy ': tys) state state

  CFunc :: T.HList SEntry stack -> T.ListPointer calls ('T.Func ('T.FuncTy inputs outputs)) ->
           StackCode stores calls (T.Append (T.Map 'Val inputs) stack)
                                  (T.Append (T.Map 'Val outputs) stack) state state
  CProc :: ValidProcParams args stack_with_inputs stack ->
           T.ListPointer calls ('T.Proc ('T.ProcTy args)) ->
           StackCode stores calls stack_with_inputs stack 'Ready 'Ready

  CStop   :: StackCode stores calls a b state1 state2

  CWhile :: StackCode stores calls stack ('Val 'T.BoolTy ': stack) state state ->
            StackCode stores calls stack stack state state ->
            StackCode stores calls stack stack state state

  CDecls :: Declarations tys stores calls -> StackCode (T.Append tys stores) calls stack1 stack2 state1 state2 -> StackCode stores calls stack1 stack2 state1 state2
  SkipDecl :: T.SStoreTy ty -> StackCode stores calls stack1 stack2 state1 state2 -> StackCode (ty ': stores) calls stack1 stack2 state1 state2
  EmptyDecls :: T.HList T.SStoreTy tys -> StackCode (T.Append tys stores) calls stack1 stack2 state1 state2 -> StackCode stores calls stack1 stack2 state1 state2

  CAlts :: StackCode stores calls tys tys ('Alt tys2) ('Alt tys2) ->
           StackCode stores calls tys tys2 'Ready 'Ready

  CAltBranch ::  T.SCast ch ('T.ChanInput ty) ->
                 T.SNat n ->
                 StackCode stores calls (T.Append (T.Repeat ('Val 'T.IntTy) n) ('Val ty ': tys)) tys2 'Ready 'Ready ->
                 StackCode stores calls (T.Append (T.Repeat ('Val 'T.IntTy) n) ('Ref ('T.Chan ch) ': tys)) tys ('Alt tys2) ('Alt tys2)
  CTimeBranch :: T.SNat n ->
                 StackCode stores calls (T.Append (T.Repeat ('Val 'T.IntTy) n) tys) tys2 'Ready 'Ready ->
                 StackCode stores calls (T.Append (T.Repeat ('Val 'T.IntTy) n) ('Val 'T.IntTy ': tys)) tys ('Alt tys2) ('Alt tys2)

  CStartPars :: StackCode stores calls tys tys 'Ready 'Par
  CParBranch :: StackCode stores calls tys '[] 'Ready 'Done -> StackCode stores calls tys tys 'Par 'Par
  CEndPars :: StackCode stores calls tys tys 'Par 'Ready

  CParIndexed :: StackCode stores calls ('Val 'T.IntTy ': tys) '[] 'Ready 'Done -> StackCode stores calls ('Val 'T.IntTy ': 'Val 'T.IntTy ': tys) tys 'Ready 'Ready

  CEndProc :: StackCode stores calls stack '[] 'Ready 'Done

  CParamDecls :: ProcParams args2 s -> StackCode (T.Append (P.Args2Store args2) stores) calls stack1 stack2 state1 state2 -> StackCode stores calls stack1 stack2 state1 state2
  CStoreParamArgs :: ProcParams args2 stack2 -> StackCode stores1 calls stack2 '[] 'Ready 'Ready

deriving instance Show (Finite n)
deriving instance Show (T.HList SEntry stack)
deriving instance Show (Declarations tys stores calls)
deriving instance Show (ValidProcParams inputs stack1 stack2)
deriving instance Show (StackCode stores calls stack1 stack2 state1 state2)

data SEntry :: StackEntry -> Type where
  SRef :: T.SStoreTy ty -> SEntry ('Ref ty)
  SVal :: T.SBaseTy ty -> SEntry ('Val ty)

deriving instance Show (SEntry ty)

data ValidProcParams :: [T.ProcArg] -> [StackEntry] -> [StackEntry] -> Type where
  VPPNil :: ValidProcParams '[] stack stack
  VPPAddBase :: T.SBaseTy ty ->
                ValidProcParams inputs old_stack new_stack ->
                ValidProcParams ('T.ProcConst ty ': inputs) ('Val ty ': old_stack) new_stack
  VPPAddVar ::  T.SVarTy ty ->
                ValidProcParams inputs old_stack new_stack ->
                ValidProcParams ('T.ProcVar ty ': inputs) ('Ref ('T.Var ty) ': T.Append (T.Repeat ('Val 'T.IntTy) (C.VarDimension ty)) old_stack) new_stack
  VPPAddChan :: T.SCast stack_type param_type ->
                ValidProcParams inputs old_stack new_stack ->
                ValidProcParams ('T.ProcChan param_type ': inputs) ('Ref ('T.Chan stack_type) ': T.Append (T.Repeat ('Val 'T.IntTy) (C.ChanDimension stack_type)) old_stack) new_stack

infixr 5 :.

compileVarLocation :: E.VarLocation stores calls ty ->
                        StackCode stores calls ts ('Ref ('T.Var ty)  ': T.Append (T.Repeat ('Val 'T.IntTy) (C.VarDimension ty)) ts) state state
compileVarLocation (E.Var pointer) = CVar pointer
compileVarLocation (E.Index loc index) = compileVarLocation loc :. CSwap :. compileExpr index :. CMul :. CIndexV

compileChanLocation :: E.ChanLocation stores calls ty ->
                        StackCode stores calls ts ('Ref ('T.Chan ty)  ': T.Append (T.Repeat ('Val 'T.IntTy) (C.ChanDimension ty)) ts) state state
compileChanLocation (E.Var pointer) = CVar pointer
compileChanLocation (E.Index loc index) = compileChanLocation loc :. CSwap :. compileExpr index :. CMul :. CIndexC

compileExpr :: E.Expr stores calls t -> StackCode stores calls ts ('Val t ': ts) state state
compileExpr E.Unit                     = CLit E.UnitLit
compileExpr (E.Add e1 e2)              = compileExpr e1
                                          :. compileExpr e2
                                          :. CPlus
compileExpr (E.Mul e1 e2)              = compileExpr e1
                                          :. compileExpr e2
                                          :. CMul
compileExpr (E.Div e1 e2)              = compileExpr e1
                                          :. compileExpr e2
                                          :. CDiv
compileExpr (E.Mod e1 e2)              = compileExpr e1
                                          :. compileExpr e2
                                          :. CMod
compileExpr (E.Neg e)                  = compileExpr e
                                          :. CNeg
compileExpr (E.And [])                 = CLit $ E.BoolLit True
compileExpr (E.And [e])                = compileExpr e
compileExpr (E.And (e : e2 : es))      = compileExpr e
                                          :. CIf (CLit $ E.BoolLit True)
                                                 (compileExpr $ E.And (e2 : es))
compileExpr (E.Or [])                  = CLit $ E.BoolLit False
compileExpr (E.Or [e])                 = compileExpr e
compileExpr (E.Or (e : e2 : es))       = compileExpr e
                                          :. CIf (CLit $ E.BoolLit False)
                                                 (compileExpr $ E.Or (e2 : es))
compileExpr (E.Not e)                  = compileExpr e
                                          :. CNot
compileExpr (E.CompareEQ e1 e2)        = compileExpr e1
                                          :. compileExpr e2
                                          :. CEq
compileExpr (E.CompareGT e1 e2)        = compileExpr e2
                                          :. compileExpr e1
                                          :. CCompGT
compileExpr (E.CompareGE e1 e2)        = compileExpr (E.Not $ E.CompareGT e2 e1)
compileExpr (E.Literal a)              = CLit a
compileExpr (E.Variable location)      = compileVarLocation location :. CLookup
compileExpr (E.If eb e1 e2)            = compileExpr eb
                                          :. CIf (compileExpr e1) (compileExpr e2)
compileExpr (E.FCall pointer params)   = helper params :. CFunc undefined pointer
                                          where
                                            helper :: T.HList (E.Expr stores calls) inputs ->
                                                      StackCode stores calls stack (T.Append (T.Map 'Val inputs) stack) state state
                                            helper T.HNil = CNil
                                            helper (T.HCons expr rest) = helper rest :. compileExpr expr
compileExpr (E.Length loc) = helper FZ loc
                              where
                                helper :: Finite (C.VarDimension ty) ->
                                          E.VarLocation stores calls ('T.Arr ty) ->
                                          StackCode stores calls st ('Val 'T.IntTy ': st) state state
                                helper n (E.Var pos) = CArrElemSize pos (FS n) :. CArrElemSize pos (inject n) :. CDiv
                                helper n (E.Index pos _) = helper (FS n) pos
compileExpr (E.ChanLength loc) = helper FZ loc
                                  where
                                    helper :: Finite (C.ChanDimension ty) ->
                                              E.ChanLocation stores calls ('T.ChanArr ty) ->
                                              StackCode stores calls st ('Val 'T.IntTy ': st) state state
                                    helper n (E.Var pos) = CChanArrElemSize pos (FS n) :. CChanArrElemSize pos (inject n) :. CDiv
                                    helper n (E.Index pos _) = helper (FS n) pos

inject :: Finite n -> Finite ('T.Succ n)
inject FZ = FZ
inject (FS n) = FS (inject n)

data Declarations :: [T.StoreTy] -> [T.StoreTy] -> [T.CallTy] -> Type where
  DNil :: Declarations '[] stores calls
  DVar :: T.SVarTy ty -> C.Vect (C.VarDimension ty) (StackCode stores calls stack ('Val 'T.IntTy ': stack) st st) -> Declarations tys stores calls -> Declarations ('T.Var ty ': tys) stores calls
  DChan :: T.SChanTy ty -> C.Vect (C.ChanDimension ty) (StackCode stores calls stack ('Val 'T.IntTy ': stack) st st) -> Declarations tys stores calls -> Declarations ('T.Chan ty ': tys) stores calls

compileCommon :: forall k stores calls st. (forall sts cs. k sts cs -> StackCode sts cs st st 'Ready 'Ready) ->
                                            C.Common k stores calls -> StackCode stores calls st st 'Ready 'Ready
compileCommon f (C.Inj inj) = f inj
compileCommon _ (C.Assign assignment) = helper assignment
                                         where
                                           helper :: C.Assignment stores calls ->
                                                     StackCode stores calls stack stack 'Ready 'Ready
                                           helper C.NilAssign = CNil
                                           helper (C.ConsAssign _ loc expr rest) =
                                               compileExpr expr
                                               :. helper rest
                                               :. compileVarLocation loc
                                               :. CStore
compileCommon _ (C.MultiAssign func exprs locs) = compileExprs exprs
                                                 :. CFunc (undefined :: T.HList SEntry st) func
                                                 :. store_vals locs
                                                 where
                                                   compileExprs :: T.HList (E.Expr stores calls) inputs ->
                                                                    StackCode stores calls st (T.Append (T.Map 'Val inputs) st) 'Ready 'Ready
                                                   compileExprs T.HNil = CNil
                                                   compileExprs (T.HCons expr rest) = compileExprs rest :. compileExpr expr
                                                   store_vals :: T.HList (E.BaseVarLocation stores calls) outputs ->
                                                                 StackCode stores calls (T.Append (T.Map 'Val outputs) st) st 'Ready 'Ready
                                                   store_vals T.HNil = CNil
                                                   store_vals (T.HCons (E.MkComp loc) rest) = compileVarLocation loc :. CStore :. store_vals rest
compileCommon _ C.Stop = CStop
compileCommon _ (C.If []) = CNil
compileCommon f (C.If ((test, body) : rest)) = compileExpr test :. CIf (compileCommon f body)
                                                                         (compileCommon f (C.If rest))
compileCommon f (C.While e body) = CWhile (compileExpr e) (compileCommon f body)
compileCommon f body@C.DeclareVar{} = let marker = undefined :: T.HList T.SStoreTy stores
                                             in collectVarDecls marker DNil body (\decls rest ->
                                                 CDecls decls (compileCommon f rest))
compileCommon f (C.Seq bodies) = foldr ((:.) . compileCommon f) CNil bodies
compileCommon f (C.ReplSeq e1 e2 body) = compileExpr e1 :. compileExpr e2 :.
                                            CDecls
                                              (DVar (T.SBase T.SInt) C.VNil $
                                                 DVar (T.SBase T.SInt) C.VNil
                                                 DNil)
                                              (CVar T.Last
                                                :. CStore
                                                :. CVar (T.Prev T.Last)
                                                :. CStore
                                                :. CWhile (compileExpr $ E.CompareGE (E.Variable $ E.Var T.Last) (E.Variable $ E.Var (T.Prev T.Last)))
                                                          (SkipDecl (T.SVarStore $ T.SBase T.SInt) (compileCommon f body)
                                                            :. CVar (T.Prev T.Last) :. CInc))

convertDecls :: C.ValofDecls stores calls decls -> Declarations (T.Map 'T.Var decls) stores calls
convertDecls C.NilD = DNil
convertDecls (C.ConsD ty vec rest) = DVar ty (C.vectMap compileExpr vec) (convertDecls rest)

compileValof :: C.Valof stores calls res -> StackCode stores calls tys (T.Append (T.Map 'Val res) tys) 'Ready 'Ready
compileValof (C.Valof decls body exprs) = CDecls (convertDecls decls) (compileCommon (\(C.DConst v) -> absurd v) body :. do_exprs exprs)
                                            where
                                              do_exprs :: T.HList (E.Expr stores calls) rs -> StackCode stores calls tys (T.Append (T.Map 'Val rs) tys) st st
                                              do_exprs T.HNil = CNil
                                              do_exprs (T.HCons e es) = do_exprs es :. compileExpr e

hMap :: (forall t. k t -> f (c t)) -> T.HList k ts -> T.HList f (T.Map c ts)
hMap _ T.HNil = T.HNil
hMap f (T.HCons x xs) = T.HCons (f x) (hMap f xs)

hMap2 :: (forall t. k t -> f t) -> T.HList k ts -> T.HList f ts
hMap2 _ T.HNil = T.HNil
hMap2 f (T.HCons x xs) = T.HCons (f x) (hMap2 f xs)

proveAppend :: T.HList k ts -> T.PropEq (T.Append ts '[]) ts
proveAppend T.HNil = T.Refl
proveAppend (T.HCons _ rest) = case proveAppend rest of T.Refl -> T.Refl

compileFunction :: forall stores calls ins outs. C.Function stores calls ('T.FuncTy ins outs) ->
                                                 StackCode stores calls (T.Map 'Val ins) (T.Map 'Val outs) 'Ready 'Ready
compileFunction (C.Func (T.SFunc ins outs) body) = case proveAppend (hMap SVal outs) of
                                                     T.Refl ->
                                                        CDecls (decls ins) (store_params ins (positions ins) :. compileValof body)
                                                     where
                                                        decls :: T.HList T.SBaseTy ins2 -> Declarations (T.Map 'T.Var (T.Map 'T.Base ins2)) stores calls
                                                        decls T.HNil = DNil
                                                        decls (T.HCons ty rest) = DVar (T.SBase ty) C.VNil (decls rest)
                                                        positions :: T.HList T.SBaseTy ins2 -> T.HList (T.ListPointer (T.Append (T.Map 'T.Var (T.Map 'T.Base ins2)) stores)) (T.Map 'T.Var (T.Map 'T.Base ins2))
                                                        positions T.HNil = T.HNil
                                                        positions (T.HCons _ tys) = T.HCons T.Last (hMap2 T.Prev $ positions tys)
                                                        store_params :: T.HList T.SBaseTy ins2 -> -- 'phantom' variable
                                                                        T.HList (T.ListPointer stores1) (T.Map 'T.Var (T.Map 'T.Base ins2)) ->
                                                                        StackCode stores1 calls (T.Map 'Val ins2) '[] 'Ready 'Ready
                                                        store_params T.HNil T.HNil = CNil
                                                        store_params (T.HCons _ ts) (T.HCons pointer rest) = CVar pointer :. CStore :. store_params ts rest

collectVarDecls :: forall stores calls tys k res. T.HList T.SStoreTy stores ->
                                                   Declarations tys stores calls ->
                                                   C.Common k (T.Append tys stores) calls ->
                                                    (forall new_tys. Declarations new_tys stores calls ->
                                                                     C.Common k (T.Append new_tys stores) calls ->
                                                                     res
                                                    ) -> res
collectVarDecls s decls (C.DeclareVar ty dimens body) f = collectVarDecls s (DVar ty (c_dimens ty dimens) decls) body f
                                                          where
                                                            c_dimens :: T.SVarTy ty ->
                                                                        C.Vect (C.VarDimension ty) (E.Expr (T.Append tys stores) calls 'T.IntTy) ->
                                                                        C.Vect (C.VarDimension ty) (StackCode stores calls stack ('Val 'T.IntTy ': stack) st st)
                                                            c_dimens _ dimens2 = (C.vectMap (EmptyDecls (helper decls) . compileExpr) dimens2)
                                                            helper :: Declarations decl_types stores calls -> T.HList T.SStoreTy decl_types
                                                            helper DNil = T.HNil
                                                            helper (DVar svar _ rest) = T.HCons (T.SVarStore svar) (helper rest)
                                                            helper (DChan cvar _ rest) = T.HCons (T.SChanStore cvar) (helper rest)
--                                                            helper _ = error "unreachable UnboundedStack333"
collectVarDecls _ decls other f = f decls other

collectChanDecls :: forall stores calls tys res. T.HList T.SStoreTy stores ->
                                                  Declarations tys stores calls ->
                                                  P.Process (T.Append tys stores) calls ->
                                                   (forall new_tys. Declarations new_tys stores calls ->
                                                                    P.Process (T.Append new_tys stores) calls ->
                                                                    res
                                                   ) -> res
collectChanDecls s decls (P.DeclareChan ty dimens body) f = collectChanDecls s (DChan ty (c_dimens ty dimens) decls) body f
                                                            where
                                                              c_dimens :: T.SChanTy ty ->
                                                                          C.Vect (C.ChanDimension ty) (E.Expr (T.Append tys stores) calls 'T.IntTy) ->
                                                                          C.Vect (C.ChanDimension ty) (StackCode stores calls stack ('Val 'T.IntTy ': stack) st st)
                                                              c_dimens _ dimens2 = (C.vectMap (EmptyDecls (helper decls) . compileExpr) dimens2)
                                                              helper :: Declarations decl_types stores calls -> T.HList T.SStoreTy decl_types
                                                              helper DNil = T.HNil
                                                              helper (DVar svar _ rest) = T.HCons (T.SVarStore svar) (helper rest)
                                                              helper (DChan cvar _ rest) = T.HCons (T.SChanStore cvar) (helper rest)
--                                                              helper _ = error "unreachable UnboundedStack352"

collectChanDecls s decls (P.Common (C.Inj (P.DeclareChan ty dimens body))) f = collectChanDecls s decls (P.DeclareChan ty dimens body) f
collectChanDecls s decls (P.Common body@C.DeclareVar{}) f = collectVarDecls s decls body (\new_decls rest -> collectChanDecls s new_decls (P.Common rest) f)
collectChanDecls _ decls other f = f decls other


proveCastDimension :: T.SCast ty1 ty2 -> T.PropEq (C.ChanDimension ty1) (C.ChanDimension ty2)
proveCastDimension T.SRefl = T.Refl
proveCastDimension T.SBothToLeft = T.Refl
proveCastDimension T.SBothToRight = T.Refl
proveCastDimension (T.SLiftArr c) = case proveCastDimension c of T.Refl -> T.Refl

compileProc :: forall stores calls stack. P.Process stores calls -> StackCode stores calls stack stack 'Ready 'Ready
compileProc (P.Common common) = compileCommon compileProc common
compileProc (P.CallProc pointer params) = compile_params params (\code marker ->
                                                                       code
                                                                       :. CProc marker pointer)
                                           where
                                             compile_params :: T.HList (P.ProcParam stores calls) ins ->
                                                               (forall stack_and_ins.
                                                                  StackCode stores calls stack stack_and_ins 'Ready 'Ready ->
                                                                  ValidProcParams ins stack_and_ins stack ->
                                                                  res
                                                               ) -> res
                                             compile_params T.HNil cont = cont CNil VPPNil
                                             compile_params (T.HCons (P.ExprParam e) rest) cont =
                                                 compile_params rest (\code vpp ->
                                                     cont (code :. compileExpr e) (VPPAddBase (h e) vpp))
                                             compile_params (T.HCons (P.VarParam loc) rest) cont =
                                                 compile_params rest (\code vpp ->
                                                     cont (code :. compileVarLocation loc) (VPPAddVar (h2 loc) vpp))
                                             compile_params (T.HCons (P.ChanParam loc cast) rest) cont =
                                                 case proveCastDimension cast of
                                                    T.Refl ->
                                                       compile_params rest (\code vpp ->
                                                           cont (code :. compileChanLocation loc) (VPPAddChan cast vpp))
                                             h :: E.Expr s c ty -> T.SBaseTy ty
                                             h _ = undefined
                                             h2 :: E.VarLocation s c ty -> T.SVarTy ty
                                             h2 _ = undefined
compileProc (P.Input c_loc cast v_loc) = case proveCastDimension cast of
                                              T.Refl -> compileChanLocation c_loc
                                                        :. CQuery cast
                                                        :. compileVarLocation v_loc
                                                        :. CStore
compileProc (P.Output c_loc cast expr) = case proveCastDimension cast of
                                              T.Refl -> compileExpr expr
                                                        :. compileChanLocation c_loc
                                                        :. CSend cast
compileProc (P.Keyboard v_loc) = CKeyboard :. compileVarLocation v_loc :. CStore
compileProc (P.Screen expr) = compileExpr expr :. CScreen
compileProc (P.IntScreen expr) = compileExpr expr :. CIntScreen

compileProc P.Skip = CNil
compileProc (P.Par bodies) = CStartPars :. foldr ((:.) . (\b -> CParBranch (compileProc b :. CEndProc))) CNil bodies :. CEndPars
compileProc (P.ReplPar e1 e2 body) =
  let compiled_body = CDecls (DVar (T.SBase T.SInt) C.VNil DNil) $
                         compileVarLocation (E.Var T.Last)
                         :. CStore
                         :. compileProc body
  in compileExpr e1 :. compileExpr e2 :. (CParIndexed $ compiled_body :. CEndProc)

compileProc body@P.DeclareChan{} = let marker = undefined :: T.HList T.SStoreTy stores
                                          in collectChanDecls marker DNil body (\decls rest ->
                                                 CDecls decls (compileProc rest))

compileProc (P.Alt alt) = compileSkips alt :. CIf CNil (CAlts $ compileRest T.SZero (undefined :: T.HList T.SStoreTy stores) alt)

compileSkips :: P.Alt stores calls ->
                 StackCode stores calls ty ('Val 'T.BoolTy ': ty) 'Ready 'Ready
compileSkips (P.SeqAlt []) = CLit $ E.BoolLit False
compileSkips (P.SeqAlt [inner]) = compileSkipsInner inner
compileSkips (P.SeqAlt (inner : rest)) = compileSkipsInner inner
                                          :. CIf (CLit $ E.BoolLit True)
                                                 (compileSkips $ P.SeqAlt rest)
compileSkips (P.ReplAlt e1 e2 inner) = compileExpr e1 :. compileExpr e2 :.
                                         CDecls
                                           (DVar (T.SBase T.SInt) C.VNil $
                                              DVar (T.SBase T.SInt) C.VNil
                                              DNil)
                                           (CVar T.Last
                                            :. CStore
                                             :. CVar (T.Prev T.Last)
                                             :. CStore
                                             :. CLit (E.BoolLit False)
                                             :. CWhile (compileExpr $ E.CompareGT (E.Variable $ E.Var T.Last)
                                                                                   (E.Variable $ E.Var (T.Prev T.Last)))
                                                       (CIf (CLit (E.BoolLit True))
                                                            (SkipDecl (T.SVarStore $ T.SBase T.SInt) (compileSkipsInner inner))
                                                        :. CVar (T.Prev T.Last) :. CInc))

compileSkipsInner :: P.InnerAlt stores calls ->
                       StackCode stores calls ty ('Val 'T.BoolTy ': ty) 'Ready 'Ready
compileSkipsInner  (P.AltBranch test (P.SkipGuard body)) = compileExpr test
                                                             :. CDup
                                                             :. CIf (compileProc body) CNil
compileSkipsInner (P.AltBranch _ _) = CLit $ E.BoolLit False
compileSkipsInner (P.NestedAlt alt) = compileSkips alt

compileRest :: T.SNat n -> T.HList T.SStoreTy stores ->
                P.Alt (T.Append (T.Repeat ('T.Var ('T.Base 'T.IntTy)) n) stores) calls ->
                StackCode (T.Append (T.Repeat ('T.Var ('T.Base 'T.IntTy)) n) stores) calls st st ('Alt st) ('Alt st)
compileRest _ _ (P.SeqAlt []) = CNil
compileRest depth marker (P.SeqAlt (inner : rest)) = compileRestInner depth marker inner :. compileRest depth marker (P.SeqAlt rest)
compileRest depth marker (P.ReplAlt e1 e2 inner) = compileExpr e1 :. compileExpr e2 :.
                                                     CDecls
                                                       (DVar (T.SBase T.SInt) C.VNil $
                                                         DVar (T.SBase T.SInt) C.VNil
                                                         DNil)
                                                       (CVar T.Last
                                                         :. CStore
                                                         :. CVar (T.Prev T.Last)
                                                         :. CStore
                                                         :. CWhile (compileExpr $ E.CompareGT (E.Variable $ E.Var T.Last)
                                                                                               (E.Variable $ E.Var (T.Prev T.Last)))
                                                                   (SkipDecl (T.SVarStore $ T.SBase T.SInt) (compileRestInner (T.SSucc depth) marker inner)
                                                                    :. CVar (T.Prev T.Last) :. CInc))

proveRearrange :: T.SNat n -> T.HList SEntry tys -> T.PropEq (T.Append (T.Repeat ('Val 'T.IntTy) n) ('Val 'T.IntTy : tys)) ('Val 'T.IntTy : T.Append (T.Repeat ('Val 'T.IntTy) n) tys)
proveRearrange T.SZero _ = T.Refl
proveRearrange (T.SSucc n) marker = case proveRearrange n marker of T.Refl -> T.Refl

locDepthLookup :: forall n stores calls tys state. T.SNat n -> T.HList T.SStoreTy stores ->
                    StackCode (T.Append (T.Repeat ('T.Var ('T.Base 'T.IntTy)) n) stores) calls tys (T.Append (T.Repeat ('Val 'T.IntTy) n) tys) state state
locDepthLookup T.SZero _ = CNil
locDepthLookup (T.SSucc n) m = case proveRearrange (T.SSucc n) (undefined :: T.HList SEntry tys) of
                                   T.Refl ->
                                      CVar T.Last
                                      :. CLookup
                                      :. SkipDecl (T.SVarStore $ T.SBase T.SInt)
                                            (locDepthLookup n m)


locDepthStore :: forall n stores calls tys state. T.SNat n -> T.HList T.SStoreTy stores ->
                   StackCode (T.Append (T.Repeat ('T.Var ('T.Base 'T.IntTy)) n) stores) calls (T.Append (T.Repeat ('Val 'T.IntTy) n) tys) tys state state
locDepthStore T.SZero _ = CNil
locDepthStore (T.SSucc n) m = case proveRearrange n (undefined :: T.HList SEntry tys) of
                                   T.Refl ->
                                      SkipDecl (T.SVarStore $ T.SBase T.SInt)
                                          (locDepthStore n m)
                                      :. CVar T.Last
                                      :. CStore


compileRestInner :: forall n stores calls st. T.SNat n -> T.HList T.SStoreTy stores ->
                      P.InnerAlt (T.Append (T.Repeat ('T.Var ('T.Base 'T.IntTy)) n) stores) calls ->
                      StackCode (T.Append (T.Repeat ('T.Var ('T.Base 'T.IntTy)) n) stores) calls st st ('Alt st) ('Alt st)
compileRestInner depth m (P.AltBranch test (P.ChanGuard c_loc cast marker body)) = case proveCastDimension cast of
                                                                                     T.Refl ->
                                                                                       compileExpr test
                                                                                       :. CIf (compileChanLocation c_loc
                                                                                                :. locDepthLookup depth m
                                                                                                :. CAltBranch cast depth compiled_body)
                                                                                              CNil
                                                                                       where
                                                                                         compiled_body = locDepthStore depth m
                                                                                                         :. CDecls
                                                                                                              (DVar (T.SBase marker) C.VNil DNil)
                                                                                                              (CVar T.Last
                                                                                                               :. CStore
                                                                                                               :. compileProc body)

compileRestInner depth m (P.AltBranch test (P.TimeGuard time body)) = compileExpr test
                                                                        :. CIf (compileExpr time
                                                                                 :. locDepthLookup depth m
                                                                                 :. CTimeBranch depth compiled_body)
                                                                               CNil
                                                                        where
                                                                          compiled_body = locDepthStore depth m
                                                                                          :. compileProc body
compileRestInner _ _ (P.AltBranch _ (P.SkipGuard _)) = CNil
compileRestInner depth marker (P.NestedAlt alt) = compileRest depth marker alt


compileProcedure :: forall stores calls args stack. P.Procedure stores calls args -> ProcParams args stack -> StackCode stores calls stack '[] 'Ready 'Ready
compileProcedure (P.Proc (T.SProc _) proc) args = CParamDecls args (CStoreParamArgs args :. compileProc proc)

optimisePass :: StackCode stores calls xs ys st1 st2 -> (StackCode stores calls xs ys st1 st2, Bool)
optimisePass (CNeg :. CNeg :. c) = (c, True)
optimisePass (CNil :. ops) = (ops, True)
optimisePass (ops :. CNil) = (ops, True)
optimisePass (c1 :. c2) = let (new_c1, b1) = optimisePass c1
                              (new_c2, b2) = optimisePass c2
                           in
                               (new_c1 :. new_c2, b1 || b2)
optimisePass c = (c, False) -- No patterns triggered

optimise :: StackCode stores calls xs ys st1 st2 -> StackCode stores calls xs ys st1 st2
optimise code = let (new_code, code_changed) = optimisePass code in
                    if code_changed
                    then optimise new_code
                    else new_code

data CodeList :: [T.StoreTy] -> [T.CallTy] -> [T.CallTy] -> Type where
  NilCode :: CodeList stores calls '[]
  FuncCall :: T.SFuncTy ('T.FuncTy ins outs) ->
              StackCode stores calls (T.Map 'Val ins) (T.Map 'Val outs) 'Ready 'Ready ->
              CodeList stores calls tys ->
              CodeList stores calls ('T.Func ('T.FuncTy ins outs) ': tys)
  ProcCall :: T.SProcTy ('T.ProcTy args) ->
              ProcParams args stack ->
              StackCode stores calls stack '[] 'Ready 'Ready ->
              CodeList stores calls tys ->
              CodeList stores calls ('T.Proc ('T.ProcTy args) ': tys)

deriving instance Show (CodeList a b c)

data StackProgram :: Type where
  StackProc :: Prog.StaticList stores ->
          T.CallContext calls ->
          CodeList stores calls calls ->
          StackProgram

deriving instance Show StackProgram

data ProcParams :: [T.ProcArg] -> [StackEntry] -> Type where
  ParamsNil :: ProcParams '[] '[]
  ParamsBase :: T.SBaseTy ty ->
             ProcParams inputs stack ->
             ProcParams ('T.ProcConst ty ': inputs) ('Val ty ': stack)
  ParamsVar ::  T.SVarTy ty ->
             ProcParams inputs stack ->
             ProcParams ('T.ProcVar ty ': inputs) ('Ref ('T.Var ty) ': T.Append (T.Repeat ('Val 'T.IntTy) (C.VarDimension ty)) stack)
  ParamsChan :: T.SChanTy ty ->
             ProcParams inputs stack ->
             ProcParams ('T.ProcChan ty ': inputs) ('Ref ('T.Chan ty) ': T.Append (T.Repeat ('Val 'T.IntTy) (C.ChanDimension ty)) stack)

deriving instance Show (ProcParams args stack)

calculateParams :: T.HList T.SProcArg args -> (forall stacks. ProcParams args stacks -> res) -> res
calculateParams T.HNil f = f ParamsNil
calculateParams (T.HCons (T.SConstArg ty) rest) f = calculateParams rest (\vpp -> f (ParamsBase ty vpp))
calculateParams (T.HCons (T.SVarArg ty) rest) f = calculateParams rest (\vpp -> f (ParamsVar ty vpp))
calculateParams (T.HCons (T.SChanArg ty) rest) f = calculateParams rest (\vpp -> f (ParamsChan ty vpp))


compileProgram :: Prog.Program -> StackProgram
compileProgram (Prog.Prog stats context calls) = StackProc stats context (helper context calls)
  where helper :: T.CallContext calls2 ->
                  Prog.CallList stores calls calls2 ->
                  CodeList stores calls calls2
        helper T.NilC Prog.NilCalls = NilCode
        helper (T.ConsC _ (T.SFuncCall f_ty) rest) (Prog.FuncCall func rest2) =
            FuncCall f_ty (compileFunction func) $ helper rest rest2
        helper (T.ConsC _ (T.SProcCall (T.SProc p_ty)) rest) (Prog.ProcCall proc rest2) =
            calculateParams p_ty (\vpp ->
              ProcCall (T.SProc p_ty) vpp (compileProcedure proc vpp) $ helper rest rest2
            )
