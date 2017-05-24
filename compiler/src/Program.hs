{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE ImpredicativeTypes  #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeInType          #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE StandaloneDeriving, DeriveGeneric #-}

module Program where

import           Data.Kind    (Type)
import           GHC.Base     (assert)

import qualified Common       as C
import qualified Expressions  as E
import qualified Process      as P
import qualified RawAST       as R
import qualified Types        as T

data Static :: T.StoreTy -> Type where
  StaticChan :: T.SChanTy ty -> [Int] -> Static ('T.Chan ty)
  StaticVal :: T.SVarTy ty -> E.Literal ty -> Static ('T.Var ty)

deriving instance Show (Static a)

data StaticList :: [T.StoreTy] -> Type where
  NilStatics :: StaticList '[]
  ConsStatics :: Static ty -> StaticList xs -> StaticList (ty ': xs)

deriving instance Show (StaticList a)

data CallList :: [T.StoreTy] -> [T.CallTy] -> [T.CallTy] -> Type where
  NilCalls :: CallList stores calls '[]
  FuncCall :: C.Function stores calls f_ty ->
              CallList stores calls tys ->
              CallList stores calls ('T.Func f_ty ': tys)
  ProcCall :: P.Procedure stores calls p_ty ->
              CallList stores calls tys ->
              CallList stores calls ('T.Proc ('T.ProcTy p_ty) ': tys)

deriving instance Show (CallList a b c)

data Program :: Type where
  Prog :: StaticList stores ->
          T.CallContext calls ->
          CallList stores calls calls ->
          Program

deriving instance Show Program

readProgram :: R.Program -> T.ErrorM Program
readProgram p = readStatics (R._statics p)                              (\stats store_context ->
                readHeaders (R._functions p) (R._procedures p)          (\call_context ->
                let contexts = T.Contexts store_context call_context
                in  Prog stats call_context <$> readCalls (R._functions p) (R._procedures p) contexts
                ))

readStatics :: [R.Static] -> (forall stores. StaticList stores -> T.StoreContext stores -> T.ErrorM k) -> T.ErrorM k
readStatics [] f = f NilStatics T.NilC
readStatics (R.Static name (R.StaticChan dims base) : rest) f = case T.liftChanTy (iterate T.ChanArr (T.ChanBoth base) !! length dims) of
                                                                  T.TyWrap ty _ ->
                                                                    readStatics rest (\list context -> f (ConsStatics (StaticChan ty dims) list) (T.ConsC name (T.SChanStore ty) context))
readStatics (R.Static name (R.StaticVal ty lit) : rest) f = case T.liftVarTy ty of
                                                               T.TyWrap l_ty _ ->
                                                                 E.readLiteral l_ty lit >>= (\literal ->
                                                                   readStatics rest (\list context -> f (ConsStatics (StaticVal l_ty literal) list) (T.ConsC name (T.SVarStore l_ty) context)))

toHList :: forall a k (f :: k -> Type) res. [a] -> (a -> (forall ty. f ty -> res) -> res) -> (forall tys. T.HList f tys -> res) -> res
toHList [] _ cont = cont T.HNil
toHList (x : xs) t_f cont = t_f x (\hx -> toHList xs t_f (\hxs -> cont $ T.HCons hx hxs))

liftBaseTy :: T.BaseTy -> (forall ty. T.SBaseTy ty -> k) -> k
liftBaseTy ty f = case T.liftBaseTy ty of T.TyWrap marker _ -> f marker

liftProcArg :: T.ProcArg -> (forall arg. T.SProcArg arg -> k) -> k
liftProcArg (T.ProcConst base) cont = liftBaseTy base (\ty -> cont $ T.SConstArg ty)
liftProcArg (T.ProcVar ty) cont = case T.liftVarTy ty of T.TyWrap marker _ -> cont $ T.SVarArg marker
liftProcArg (T.ProcChan ty) cont = case T.liftChanTy ty of T.TyWrap marker _ -> cont $ T.SChanArg marker

readHeaders :: [R.Function] -> [R.Procedure] -> (forall calls. T.CallContext calls -> k) -> k
readHeaders (fun : funs) ps cont = toHList (R._fParams fun) (liftBaseTy . snd) (\(params :: T.HList T.SBaseTy ins) ->
                                   toHList (R._fResultType fun) liftBaseTy (\(results :: T.HList T.SBaseTy outs) ->
                                   readHeaders funs ps (\c ->
                                   cont $ T.ConsC (R._fName fun) (T.SFuncCall $ T.SFunc params results) c)))
readHeaders [] (proc : procs) cont = toHList (R._pParams proc) (liftProcArg . snd) (\params ->
                                     readHeaders [] procs (\c ->
                                     cont $ T.ConsC (R._pName proc) (T.SProcCall $ T.SProc params) c))
readHeaders [] [] cont = cont T.NilC

appendHList :: T.HList f tys1 -> T.HList f tys2 -> T.HList f (T.Append tys1 tys2)
appendHList T.HNil hys = hys
appendHList (T.HCons hx hxs) hys = T.HCons hx (appendHList hxs hys)

readCalls :: [R.Function] -> [R.Procedure] -> T.Contexts stores calls -> T.ErrorM (CallList stores calls calls)
readCalls fs ps c = helper fs ps c (T._calls c)
                    where
                      helper :: forall stores calls calls2. [R.Function] -> [R.Procedure] -> T.Contexts stores calls -> T.CallContext calls2 -> T.ErrorM (CallList stores calls calls2)
                      helper (fun : funs) procs c1 (T.ConsC name (T.SFuncCall (T.SFunc hins houts)) rest) =
                        let
                          rename :: [T.Ident] -> T.HList T.SBaseTy tys -> T.StoreContext tys2 -> T.ErrorM (T.StoreContext (T.Append (T.Map 'T.Var (T.Map 'T.Base tys)) tys2))
                          rename [] T.HNil c2 = Right c2
                          rename (ident : idents) (T.HCons ty rest2) c2 = T.ConsC ident (T.SVarStore . T.SBase $ ty) <$> rename idents rest2 c2
                          rename _ _ _ = Left . T.InterpretError $ "readCallsError"
                          new_stores = rename (map fst (R._fParams fun)) hins $ T._stores c1
                          new_context = T.Contexts <$> new_stores <*> pure (T._calls c1)
                          body = new_context >>= (\ c3 -> C.readValof c3 houts (R._fBody fun))
                          function = C.Func (T.SFunc hins houts) <$> body
                        in
                          assert (name == R._fName fun) $
                            FuncCall <$> function <*> helper funs procs c1 rest
                      helper [] (p : procs) c1 (T.ConsC name (T.SProcCall (T.SProc hins)) rest) =
                        let
                          rename :: [T.Ident] -> T.HList T.SProcArg tys -> T.StoreContext tys2 -> T.ErrorM (T.StoreContext (T.Append (P.Args2Store tys) tys2))
                          rename [] T.HNil c2 = Right c2
                          rename (ident : idents) (T.HCons (T.SConstArg ty) rest2) c2 = T.ConsC ident (T.SVarStore $ T.SBase ty) <$> rename idents rest2 c2
                          rename (ident : idents) (T.HCons (T.SVarArg (T.SBase ty)) rest2) c2 = T.ConsC ident (T.SRefStore ty) <$> rename idents rest2 c2
                          rename (ident : idents) (T.HCons (T.SVarArg (T.SArr ty)) rest2) c2 = T.ConsC ident (T.SVarStore $ (T.SArr ty)) <$> rename idents rest2 c2
                          rename (ident : idents) (T.HCons (T.SChanArg ty) rest2) c2 = T.ConsC ident (T.SChanStore ty) <$> rename idents rest2 c2
                          rename _ _ _ = Left . T.InterpretError $ "readCallsError"
                          new_stores = rename (map fst (R._pParams p)) hins $ T._stores c1
                          new_context = T.Contexts <$> new_stores <*> pure (T._calls c1)
                          proc = do new_c <- new_context
                                    body <- P.readProc new_c $ R._pBody p
                                    return $ P.Proc (T.SProc hins) body
                        in
                          assert (name == R._pName p) $
                            ProcCall <$> proc <*> helper [] procs c1 rest
                      helper [] [] _ T.NilC = let (nil :: CallList stores calls '[]) = NilCalls in Right nil
                      helper _ _ _ _ =  Left . T.InterpretError $ "readCallsError"