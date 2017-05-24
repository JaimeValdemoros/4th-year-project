{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveFunctor       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies        #-}
{-# LANGUAGE TypeOperators       #-}
{-# LANGUAGE FlexibleInstances #-}

module Export where

import           Data.Kind                (Type)

import           Data.Char                (ord)
import           Data.Int                 (Int32)
import qualified Data.Map.Lazy as Map
import Data.Binary
import Data.Binary.Put
import qualified Data.ByteString.Lazy as BS

import qualified Control.Monad.State.Lazy as ST

import qualified Common                   as C
import qualified Expressions              as E
import qualified Types                    as T
import qualified UnboundedStack           as U
import qualified Process as P
import qualified Program as Prog

data Op a = NOP | SWAP | DUP | INC | DEC | ADD | MUL | DIV | MOD
          | NEG | EQ | AND | OR | NOT | GT | Lit(Int32)
          | KEY | SCR | TIME
          | LDW | STW | LOCAL(Word8) | FP
          | NewFrame | DropFrame
          | NewArr | NewChan | NewChanArr
          | ChanRead | ChanWrite
          | StartAlts | AltBranch(Word8) | TimeBranch(Word8) | EndAlts
          | StartPars | ParBranch | EndPars | IndexPar
          | EndProc | Stop
          | Jump | CJump | LabelLit(a)
          deriving (Show, Functor)

instance Binary (Op Int32) where
  put NOP = put (0 :: Word8)
  put SWAP = put (1 :: Word8)
  put DUP = put (2 :: Word8)
  put INC  = put (3 :: Word8)
  put DEC = put (4 :: Word8)
  put ADD = put (5 :: Word8)
  put MUL = put (6 :: Word8)
  put DIV = put (7 :: Word8)
  put MOD = put (8 :: Word8)
  put NEG = put (9 :: Word8)
  put Export.EQ = put (10 :: Word8)
  put AND = put (11 :: Word8)
  put OR = put (12 :: Word8)
  put NOT = put (13 :: Word8)
  put Export.GT = put (14 :: Word8)
  put LDW = put (15 :: Word8)
  put STW = put (16 :: Word8)
  put FP = put (17 :: Word8)
  put NewArr = put (18 :: Word8)
  put NewChan = put (19 :: Word8)
  put NewChanArr = put (20 :: Word8)
  put NewFrame = put (21 :: Word8)
  put DropFrame = put (22 :: Word8)
  put ChanRead = put (23 :: Word8)
  put ChanWrite = put (24 :: Word8)
  put StartAlts = put (25 :: Word8)
  put EndAlts = put (26 :: Word8)
  put StartPars = put (27 :: Word8)
  put ParBranch = put (28 :: Word8)
  put EndPars = put (29 :: Word8)
  put IndexPar = put (30 :: Word8)
  put EndProc = put (31 :: Word8)
  put (AltBranch n) = if n < 32 then put (32 + n :: Word8) else error ""
  put (TimeBranch n) = if n < 32 then put (64 + n :: Word8) else error ""
  put Jump = put (97 :: Word8)
  put CJump = put (98 :: Word8)
  put KEY = put (99 :: Word8)
  put SCR = put (100 :: Word8)
  put Stop = put (101 :: Word8)
  put (LOCAL n) = if n < 128 then put (128 + n :: Word8) else error ""
  put (Lit n) = put (102 :: Word8) >> put (n :: Int32)
  put (LabelLit n) = put (102 :: Word8) >> put (n :: Int32)
  get = undefined


make_labels :: [Tagged (Op Label)] -> [Op Int32]
make_labels input = let lab_map :: Map.Map Label Int32 = (foldr (\(pos, T labs _ _) map -> foldr (\lab m2 -> Map.insert lab pos m2) map labs) Map.empty $ zip [0..] input)
                    in map (\(T _ a _) -> fmap (\lab -> (Map.!) lab_map lab) a) input


write :: String -> [Op Int32] -> IO ()
write file ops = BS.writeFile file $ runPut (mapM_ put ops)

data Frame :: [T.StoreTy] -> Type where
  NilFrame :: Frame '[]
  SkipFrame :: T.SStoreTy ty -> Frame (ty ': tys) -> Frame tys
  ConsFrame :: T.HList T.SStoreTy tys1 -> Frame tys2 -> Frame (T.Append tys1 tys2)
  ImaginaryVars :: T.HList T.SStoreTy tys1 -> Frame tys2 -> Frame (T.Append tys1 tys2)

varInfo :: Frame tys -> T.ListPointer tys ty -> [Tagged (Op Label)]
varInfo f loc = simple FP ++ (helper f loc)
                  where
                    helper :: Frame tys -> T.ListPointer tys ty -> [Tagged (Op Label)]
                    helper (ConsFrame (T.HCons ty rest) _) T.Last =
                      let pos = frame_pos rest
                          n = dimen ty
                      in if n > 0 then simples [Lit . fromIntegral $ (pos + n-1), ADD]
                                         ++ (concat $ take (n-1) $ repeat (simples [DUP, LDW, SWAP, Lit(-1), ADD]))
                                         ++ (simples [Lit 1, SWAP, LDW])
                                  else simples [Lit . fromIntegral $ (pos + n), ADD]
                      where
                        frame_pos :: T.HList T.SStoreTy tys1 -> Int
                        frame_pos T.HNil = 0
                        frame_pos (T.HCons t lowers) = 1 + dimen t + frame_pos lowers
                        dimen :: T.SStoreTy ty -> Int
                        dimen (T.SVarStore t) = dimen1 t
                        dimen (T.SChanStore t) = dimen2 t
                        dimen (T.SRefStore _) = 1
                        dimen1 :: T.SVarTy t -> Int
                        dimen1 (T.SArr t) = 1 + dimen1 t
                        dimen1 _ = 0
                        dimen2 :: T.SChanTy ty -> Int
                        dimen2 (T.SChanArr t) = 1 + dimen2 t
                        dimen2 _ = 0
                    helper (ConsFrame (T.HCons _ rest) next_frame) (T.Prev p) =
                      helper (ConsFrame rest next_frame) p
                    helper (ConsFrame T.HNil prev_frame) pos = (simples [Lit (-1), ADD, LDW])
                                                               ++ helper prev_frame pos
                    helper (SkipFrame _ (ConsFrame (T.HCons _ rest) prev_frame)) pos =
                      helper (ConsFrame rest prev_frame) pos
                    helper (SkipFrame t (ConsFrame T.HNil prev_frame)) pos =
                      (simples [Lit (-1), ADD, LDW]) ++ helper (SkipFrame t prev_frame) pos
                    helper (SkipFrame _ (ImaginaryVars (T.HCons _ rest) prev_frame)) pos =
                      helper (ImaginaryVars rest prev_frame) pos
                    helper (ImaginaryVars T.HNil rest) pointer =
                      helper rest pointer
                    helper (SkipFrame t (ImaginaryVars T.HNil prev_frame)) pos =
                      helper (SkipFrame t prev_frame) pos
                    helper (ImaginaryVars (T.HCons _ _) _) T.Last =
                      error "Referencing an undeclared variable"
                    helper (ImaginaryVars (T.HCons _ rest) realvars) (T.Prev p) =
                      helper (ImaginaryVars rest realvars) p
                    helper _ _ = error "unimplemented"

type Label = String

freshLabel :: ST.State Int Label
freshLabel = ST.modify (+1) >> ST.get >>= (return . show)

data Tagged a = T [Label] a String deriving Show

mark :: Label -> [Tagged (Op a)] -> [Tagged (Op a)]
mark label [] = [T [label] NOP ""]
mark label (T labels x comment : rest) = (T (label : labels) x comment) : rest

simple :: Op label -> [Tagged (Op label)]
simple op = [T [] op ""]

simples :: [Op label] -> [Tagged (Op label)]
simples = concatMap simple

type family Length (list :: [k]) :: T.Nat where
    Length '[] = 'T.Zero
    Length (x ': xs) = 'T.Succ (Length xs)

toList :: C.Vect n ty -> [ty]
toList C.VNil = []
toList (C.VCons x rest) = x : toList rest

convertAll :: U.StackProgram -> [[Tagged (Op Label)]]
convertAll (U.StackProc statics context code) = (:) [T [] (LabelLit "done") "",
                                                      T [] (LabelLit "procedure0") "",
                                                      T [] Jump "",
                                                      T ["done"] EndProc ""] $ map (\c -> c ++ [T [] Jump ""]) $ ST.evalState (code2 0 statics context code) 0
                                                where
                                                  frame :: Prog.StaticList stores -> Frame stores
                                                  frame statics = case U.proveAppend (helper1 statics) of T.Refl -> ConsFrame (helper1 statics) NilFrame
                                                  labs :: T.CallContext calls -> C.Vect (Length calls) Label
                                                  labs = helper2 0
                                                  helper1 :: Prog.StaticList stores2 -> T.HList T.SStoreTy stores2
                                                  helper1 Prog.NilStatics = T.HNil
                                                  helper1 (Prog.ConsStatics (Prog.StaticChan ty _) rest) = T.HCons (T.SChanStore ty) (helper1 rest)
                                                  helper1 (Prog.ConsStatics (Prog.StaticVal ty _) rest) = T.HCons (T.SVarStore ty) (helper1 rest)
                                                  helper2 :: Int -> T.CallContext calls2 -> C.Vect (Length calls2) Label
                                                  helper2 _ T.NilC = C.VNil
                                                  helper2 n (T.ConsC _ (T.SFuncCall _) rest) = C.VCons ("function" ++ show n) (helper2 (n+1) rest)
                                                  helper2 n (T.ConsC _ (T.SProcCall _) rest) = C.VCons ("procedure" ++ show n) (helper2 (n+1) rest)
                                                  code2 :: Int -> Prog.StaticList stores -> T.CallContext calls -> U.CodeList stores calls calls2 ->ST.State Int [[Tagged (Op Label)]]
                                                  code2 n _ _ U.NilCode = return []
                                                  code2 n s c (U.FuncCall _ code rest) = do head <- stConvert (frame s) (labs c) code Nothing
                                                                                            tail <- code2 (n+1) s c rest
                                                                                            return (mark ("function" ++ show n) head : tail)
                                                  code2 n s c (U.ProcCall _ _ code rest) = do head <- stConvert (frame s) (labs c) code Nothing
                                                                                              tail <- code2 (n+1) s c rest
                                                                                              return (mark ("procedure" ++ show n) head : tail)

jump :: Label -> [Tagged (Op Label)]
jump lab = [T [] (LabelLit lab) "", T [] Jump ""]

cjump :: Label -> [Tagged (Op Label)]
cjump lab = [T [] (LabelLit lab) "", T [] CJump ""]

stConvert :: Frame stores ->
             C.Vect (Length calls) Label ->
             U.StackCode stores calls a b st1 st2 ->
             Maybe Label -> -- exit label
             ST.State Int [Tagged (Op Label)]
stConvert c l ((U.:.) code1 code2) elab = (++) <$> stConvert c l code1 elab <*> stConvert c l code2 elab
stConvert _ _ U.CNil _ = return $ simple NOP
stConvert _ _ U.CSwap _= return $ simple SWAP
stConvert _ _ U.CDup _ = return $ simple DUP
stConvert _ _ U.CInc _ = return $ simple INC
stConvert _ _ U.CDec _ = return $ simple DEC
stConvert _ _ U.CPlus _ = return $ simple ADD
stConvert _ _ U.CMul _ = return $ simple MUL
stConvert _ _ U.CDiv _ = return $ simple DIV
stConvert _ _ U.CMod _ = return $ simple MOD
stConvert _ _ U.CNeg _ = return $ simple NEG
stConvert _ _ U.CEq _ = return $ simple Export.EQ
stConvert _ _ U.CAnd _ = return $ simple AND
stConvert _ _ U.COr _ = return $ simple OR
stConvert _ _ U.CNot _ = return $ simple NOT
stConvert _ _ U.CCompGT _ = return $ simple Export.GT
stConvert _ _ (U.CLit lit) _ = return $ simple (Lit $ convert_literal lit)
stConvert c l (U.CIf t_branch f_branch) elab = do fs <- stConvert c l f_branch elab
                                                  ts <- stConversut c l t_branch elab
                                                  t_label <- freshLabel
                                                  exit_label <- freshLabel
                                                  return $ (cjump t_label)
                                                           ++ fs
                                                           ++ (jump exit_label)
                                                           ++ (mark t_label ts)
                                                           ++ (mark exit_label [])
--stConvert _ _ U.CShift = return $ simple SHIFT
stConvert _ _ U.CLookup _ = return $ simple LDW
stConvert _ _ U.CStore _ = return $ simple STW
stConvert _ _ U.CIndexV _ = return $ simple ADD
stConvert _ _ U.CIndexC _ = return $ simple ADD
stConvert _ _ U.CKeyboard _ = return $ simple KEY
stConvert _ _ U.CScreen _ = return $ simple SCR
stConvert _ _ U.CIntScreen _ = return $ simple SCR
stConvert _ _ (U.CQuery _) _ = return $ simples [LDW, ChanRead]
stConvert _ _ (U.CSend _) _ = return $ simples [LDW, ChanWrite]
stConvert c _ (U.CVar pointer) _ = return $ varInfo c pointer

stConvert _ _ (U.CArrElemSize pointer nth) _ = undefined pointer nth
stConvert _ _ (U.CChanArrElemSize pointer nth) _ = undefined pointer nth
stConvert _ l (U.CFunc _ p) _ = do return_label <- freshLabel
                                   return $ simples [LabelLit return_label, LabelLit (read_pointer p l), Jump] ++ [T [return_label] NOP ""]
stConvert _ l (U.CProc _ p) _ = do return_label <- freshLabel
                                   return $ simples [LabelLit return_label, LabelLit (read_pointer p l), Jump] ++ [T [return_label] NOP ""]
stConvert _ _ U.CStop _ = return $ simple Stop
stConvert c l (U.CWhile test body) elab = do start_label <- freshLabel
                                             exit_label <- freshLabel
                                             t <- stConvert c l test Nothing
                                             b <- stConvert c l body elab
                                             return $ (mark start_label t)
                                                       ++ simple NOT
                                                       ++ cjump exit_label
                                                       ++ b
                                                       ++ jump start_label
                                                       ++ (mark exit_label [])
stConvert c l (U.CDecls decls body) elab = let (size, declare_code, typelist) = stConvertDecls c l decls
                                            in do c_body <- stConvert (ConsFrame typelist c) l body elab
                                                  declare <- declare_code
                                                  return (simple (Lit . fromIntegral $ size)
                                                         ++ simple NewFrame
                                                         ++ declare
                                                         ++ c_body
                                                         ++ simple DropFrame)
                                            where
                                              stConvertDecls :: Frame stores ->
                                                                 C.Vect (Length calls) Label ->
                                                                 U.Declarations decls stores calls ->
                                                                      ( Word8
                                                                      , ST.State Int [Tagged (Op Label)]
                                                                      , T.HList T.SStoreTy decls
                                                                      )
                                              stConvertDecls _ _ U.DNil = (0, return [], T.HNil)
                                              stConvertDecls c2 labs (U.DVar ty dims rest) =
                                                case stConvertDecls c2 labs rest of
                                                  (size, init_code, tys) ->
                                                    let new_size = size + 1 + (fromIntegral $ v_length dims)
                                                        new_init = if v_length dims == 0 then init_code
                                                                   else do l_init_code <- init_code
                                                                           dim_code <- compile_dims c2 labs dims
                                                                           return $ l_init_code ++
                                                                                    dim_code ++
                                                                                    simple DUP ++
                                                                                    simple NewArr ++
                                                                                    simple (LOCAL . fromIntegral $ size) ++
                                                                                    simple STW ++
                                                                                    concatMap (\pos -> [T [] (LOCAL pos) "", T [] STW ""])
                                                                                              [size + 1 .. size + (fromIntegral $ v_length dims)]
                                                    in (new_size, new_init, T.HCons (T.SVarStore ty) tys)
                                              stConvertDecls c2 labs (U.DChan ty dims rest) =
                                                case stConvertDecls c2 labs rest of
                                                  (size, init_code, tys) ->
                                                    let new_size = size + 1 + (fromIntegral $ v_length dims)
                                                        new_init = if v_length dims == 0
                                                                   then do l_init_code <- init_code
                                                                           return $ l_init_code
                                                                                    ++ simple NewChan
                                                                                    ++ simple (LOCAL size)
                                                                                    ++ simple STW
                                                                   else do l_init_code <- init_code
                                                                           dim_code <- compile_dims c2 labs dims
                                                                           return $ l_init_code ++
                                                                                    dim_code
                                                                                    ++ simple DUP
                                                                                    ++ simple NewChanArr
                                                                                    ++ simple (LOCAL size)
                                                                                    ++ simple STW
                                                                                    ++ concatMap (\pos -> [T [] (LOCAL pos) "", T [] STW ""])
                                                                                                 [size + 1 .. size + (fromIntegral $ v_length dims)]
                                                    in (new_size, new_init, T.HCons (T.SChanStore ty) tys)
                                              v_length :: C.Vect n ty -> Int
                                              v_length C.VNil = 0
                                              v_length (C.VCons _ rest) = 1 + v_length rest
                                              compile_dims :: Frame stores ->
                                                              C.Vect (Length calls) Label ->
                                                              C.Vect n (U.StackCode stores calls st ('U.Val 'T.IntTy ': st) state state) ->
                                                              ST.State Int [Tagged (Op Label)]
                                              compile_dims _ _ C.VNil = return []
                                              compile_dims c2 labs (C.VCons e C.VNil) = stConvert c2 labs e Nothing
                                              compile_dims c2 labs (C.VCons expr rest) = do r <- compile_dims c2 labs rest
                                                                                            e <- stConvert c2 labs expr Nothing
                                                                                            return $ r
                                                                                                     ++ simple DUP
                                                                                                     ++ e
                                                                                                     ++ simple MUL

stConvert c l (U.SkipDecl marker body) elab = stConvert (SkipFrame marker c) l body elab
stConvert c l (U.EmptyDecls marker body) elab = stConvert (ImaginaryVars marker c) l body elab
stConvert c l (U.CAlts alts) Nothing = do exit_label <- freshLabel
                                          c_body <- stConvert c l alts (Just exit_label)
                                          return $ simple StartAlts ++ c_body ++ simple EndAlts ++ mark exit_label []
stConvert c labs (U.CAltBranch _ nat body) (Just elab) = do this_label <- freshLabel
                                                            next_label <- freshLabel
                                                            c_body <- stConvert c labs body Nothing
                                                            return $ simple (LabelLit this_label)
                                                                     ++ simples [SWAP, LDW, SWAP]
                                                                     ++ simple (AltBranch . fromIntegral $ read_nat nat)
                                                                     ++ jump next_label
                                                                     ++ mark this_label c_body
                                                                     ++ jump elab
                                                                     ++ mark next_label []
stConvert c labs (U.CTimeBranch nat body) (Just elab) = do this_label <- freshLabel
                                                           next_label <- freshLabel
                                                           c_body <- stConvert c labs body Nothing
                                                           return (simple (LabelLit this_label)
                                                                   ++ simple (TimeBranch (fromIntegral $ read_nat nat))
                                                                   ++ jump next_label
                                                                   ++ mark this_label c_body
                                                                   ++ jump elab
                                                                   ++ mark next_label [])
stConvert _ _ U.CStartPars Nothing = return $ simple StartPars
stConvert c l (U.CParBranch body) Nothing = do label <- freshLabel
                                               skip_label <- freshLabel
                                               c_body <- stConvert c l body Nothing
                                               return ([ T [] (LabelLit label) ""
                                                       , T [] ParBranch ""]
                                                       ++ jump skip_label
                                                       ++ mark label c_body
                                                       ++ mark skip_label [])
stConvert _ _ U.CEndPars Nothing = return $ simple EndPars
stConvert c l (U.CParIndexed body) Nothing = do label <- freshLabel
                                                skip_label <- freshLabel
                                                c_body <- stConvert c l body Nothing
                                                return ([ T [] (LabelLit label) ""
                                                        , T [] IndexPar ""]
                                                        ++ jump skip_label
                                                        ++ mark label c_body
                                                        ++ mark skip_label [])

stConvert c l (U.CParamDecls params body) Nothing = let (size, typelist) = helper params
                                                    in
                                                      do c_body <- stConvert (ConsFrame typelist c) l body Nothing
                                                         return $ simple (Lit . fromIntegral $ size)
                                                                   ++ simple NewFrame
                                                                   ++ c_body
                                                                   ++ simple DropFrame
                                                    where
                                                      helper :: U.ProcParams args stack -> (Word8, T.HList T.SStoreTy (P.Args2Store args))
                                                      helper U.ParamsNil = (0, T.HNil)
                                                      helper (U.ParamsBase ty rest) =
                                                          let (size, typelist) = helper rest
                                                          in (size + 1, T.HCons (T.SVarStore (T.SBase ty)) typelist)
                                                      helper (U.ParamsVar (T.SBase ty) rest) =
                                                          let (size, typelist) = helper rest
                                                          in (size + 1, T.HCons (T.SRefStore ty) typelist)
                                                      helper (U.ParamsVar (T.SArr ty) rest) =
                                                          let (size, typelist) = helper rest
                                                          in (size + 1 + (fromIntegral $ dimen (T.SArr ty)), T.HCons (T.SVarStore (T.SArr ty)) typelist)
                                                          where
                                                            dimen :: T.SVarTy ty -> Int
                                                            dimen (T.SBase _) = 0
                                                            dimen (T.SArr t) = 1 + dimen t
                                                      helper (U.ParamsChan ty rest) =
                                                          let (size, typelist) = helper rest
                                                          in (size + (fromIntegral $ dimen ty), T.HCons (T.SChanStore ty) typelist)
                                                          where
                                                            dimen :: T.SChanTy ty -> Int
                                                            dimen (T.SChanArr t) = 1 + dimen t
                                                            dimen _ = 0

stConvert _ _ U.CEndProc Nothing = return $ simple EndProc
stConvert _ _ (U.CStoreParamArgs params) Nothing = return $ helper 0 params
                                                   where
                                                     helper :: Word8 -> U.ProcParams a b -> [Tagged (Op Label)]
                                                     helper _ U.ParamsNil = []
                                                     helper n (U.ParamsBase _ rest) = simples [LOCAL n, STW] ++ helper (n+1) rest
                                                     helper n (U.ParamsVar ty rest) = let k = (fromIntegral $ dimen1 ty) :: Word8 in
                                                                                      simples (concatMap (\k2 -> [LOCAL k2, STW]) $ [0..k]) ++ helper (n+k+1) rest
                                                                                      where
                                                                                        dimen1 :: T.SVarTy t -> Int
                                                                                        dimen1 (T.SArr t) = 1 + dimen1 t
                                                                                        dimen1 _ = 0
                                                     helper n (U.ParamsChan ty rest) = let k = fromIntegral $ dimen2 ty in
                                                                                       simples (concatMap (\k2 -> [LOCAL k2, STW]) $ [0..k]) ++ helper (n+k+1) rest
                                                                                       where
                                                                                         dimen2 :: T.SChanTy ty -> Int
                                                                                         dimen2 (T.SChanArr t) = 1 + dimen2 t
                                                                                         dimen2 _ = 0

convert_literal :: E.Literal ('T.Base ty) -> Int32
convert_literal E.UnitLit = 0
convert_literal (E.BoolLit False) = 0
convert_literal (E.BoolLit True) = 1
convert_literal (E.CharLit c) = fromIntegral $ ord c
convert_literal (E.IntLit i) = fromIntegral i

read_nat :: T.SNat nat -> Int
read_nat T.SZero = 0
read_nat (T.SSucc n) = 1 + read_nat n

read_pointer :: T.ListPointer vs v -> C.Vect (Length vs) k -> k
read_pointer T.Last (C.VCons x _) = x
read_pointer (T.Prev p) (C.VCons _ rest) = read_pointer p rest