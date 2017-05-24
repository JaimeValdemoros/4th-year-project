{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE PolyKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators       #-}

{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE StandaloneDeriving  #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE TypeFamilies       #-}

module Types where

import GHC.Generics(Generic)
import           Data.Kind (Type)
import           Data.Void

type Ident = String

data BaseTy = UnitTy | BoolTy | CharTy | IntTy deriving (Show, Generic)
data ChanTy = ChanInput BaseTy | ChanOutput BaseTy | ChanBoth BaseTy | ChanArr ChanTy deriving (Show, Generic)
data VarTy = Base BaseTy | Arr VarTy deriving (Show, Generic)

data StoreTy = Chan ChanTy | Var VarTy | Ref BaseTy deriving (Show, Generic)

data FuncTy = FuncTy [BaseTy] [BaseTy]  deriving (Show, Generic)-- FuncTy inputs outputs

data ProcArg = ProcConst BaseTy | ProcChan ChanTy | ProcVar VarTy deriving (Show, Generic)
data ProcTy = ProcTy [ProcArg] deriving (Show, Generic)

data CallTy = Func FuncTy | Proc ProcTy deriving (Show, Generic)

-- https://typesandkinds.wordpress.com/2012/12/01/decidable-propositional-equality-in-haskell/
data PropEq :: k -> k -> * where
  Refl :: PropEq x x

type EnumerableEquality (a :: k) (b :: k) = Maybe (PropEq a b)

-- singleton over types
data SBaseTy :: BaseTy -> * where
  SUnit :: SBaseTy 'UnitTy
  SBool :: SBaseTy 'BoolTy
  SChar :: SBaseTy 'CharTy
  SInt :: SBaseTy 'IntTy

deriving instance Show (SBaseTy ty)

data Nat = Zero | Succ Nat deriving (Show, Generic)

data SNat :: Nat -> * where
  SZero :: SNat 'Zero
  SSucc :: SNat n -> SNat ('Succ n)

deriving instance Show (SNat ty)

data SVarTy :: VarTy -> * where
  SBase :: SBaseTy ty -> SVarTy ('Base ty)
  SArr :: SVarTy ty -> SVarTy ('Arr ty)

deriving instance Show (SVarTy ty)

-- singleton over types
data SChanTy :: ChanTy -> * where
  SChanInput :: SBaseTy ty -> SChanTy ('ChanInput ty)
  SChanOutput :: SBaseTy ty -> SChanTy ('ChanOutput ty)
  SChanBoth :: SBaseTy ty -> SChanTy ('ChanBoth ty)
  SChanArr :: SChanTy ty -> SChanTy ('ChanArr ty)

deriving instance Show (SChanTy ty)

data SCast :: ChanTy -> ChanTy -> * where
  SRefl :: SCast ty ty
  SBothToLeft :: SCast ('ChanBoth ty) ('ChanInput ty)
  SBothToRight :: SCast ('ChanBoth ty) ('ChanOutput ty)
  SLiftArr :: SCast ty1 ty2 -> SCast ('ChanArr ty1) ('ChanArr ty2)

deriving instance Show (SCast ty1 ty2)

canCast :: SChanTy ty1 -> SChanTy ty2 -> Maybe (SCast ty1 ty2)
canCast (SChanArr m1) (SChanArr m2) = SLiftArr <$> canCast m1 m2
canCast (SChanBoth m1) (SChanInput m2) = (\Refl -> SBothToLeft) <$> decBaseEq m1 m2
canCast (SChanBoth m1) (SChanOutput m2) = (\Refl -> SBothToRight) <$> decBaseEq m1 m2
canCast m1 m2 = (\Refl -> SRefl) <$> decChanEq m1 m2

data HList (f :: k -> *) :: [k] -> * where
  HNil :: HList f '[]
  HCons :: f ty -> HList f tys -> HList f (ty ': tys)
--
--instance Show (HList f '[]) where
--  show HNil = "HNil"
--
--instance (Show (f ty), Show (HList f tys)) => Show (HList f (ty ': tys)) where
--  show (HCons x rest) = "(" ++ show x ++ " : " ++ show rest ++ ")"

data SFuncTy :: FuncTy -> * where
  SFunc :: HList SBaseTy ins -> HList SBaseTy outs -> SFuncTy ('FuncTy ins outs)

deriving instance (Show (HList SBaseTy ts))
deriving instance Show (SFuncTy ('FuncTy ty ty2))

data SProcArg :: ProcArg -> * where
  SConstArg :: SBaseTy ty -> SProcArg ('ProcConst ty)
  SVarArg :: SVarTy ty -> SProcArg ('ProcVar ty)
  SChanArg :: SChanTy ty -> SProcArg ('ProcChan ty)

deriving instance Show (SProcArg p)

data SProcTy :: ProcTy -> * where
  SProc :: HList SProcArg tys -> SProcTy ('ProcTy tys)

deriving instance Show (HList SProcArg tys)
deriving instance Show (SProcTy ty)

data SStoreTy :: StoreTy -> * where
  SVarStore :: SVarTy ty -> SStoreTy ('Var ty)
  SChanStore :: SChanTy ty -> SStoreTy ('Chan ty)
  SRefStore :: SBaseTy ty -> SStoreTy ('Ref ty)

deriving instance Show (SStoreTy ty)
deriving instance Show (HList SStoreTy tys)

data SCallTy :: CallTy -> * where
  SFuncCall :: SFuncTy ('FuncTy ins outs) -> SCallTy ('Func ('FuncTy ins outs))
  SProcCall :: SProcTy ty -> SCallTy ('Proc ty)

deriving instance Show (SCallTy ty)

decBaseEq :: SBaseTy a -> SBaseTy b -> EnumerableEquality a b
decBaseEq SUnit SUnit = Just Refl
decBaseEq SChar SChar = Just Refl
decBaseEq SInt SInt = Just Refl
decBaseEq _ _ = Nothing

decVarEq :: SVarTy a -> SVarTy b -> EnumerableEquality a b
decVarEq (SBase x') (SBase y') = (\Refl -> Refl) <$> decBaseEq x' y'
decVarEq (SArr x') (SArr y') = (\Refl -> Refl) <$> decVarEq x' y'
decVarEq _ _ = Nothing

decChanEq :: SChanTy a -> SChanTy b -> EnumerableEquality a b
decChanEq (SChanInput x') (SChanInput y') = (\Refl -> Refl) <$> decBaseEq x' y'
decChanEq (SChanOutput x') (SChanOutput y') = (\Refl -> Refl) <$> decBaseEq x' y'
decChanEq (SChanArr x') (SChanArr y') = (\Refl -> Refl) <$> decChanEq x' y'
decChanEq _ _ = Nothing

data TyWrapper (mark :: ty -> *) (k :: ty -> *) :: * where
  TyWrap :: mark a -> k a -> TyWrapper mark k

type VarTyWrapper = TyWrapper SVarTy
type ChanTyWrapper = TyWrapper SChanTy
type StoreTyWrapper = TyWrapper SStoreTy

type FuncTyWrapper = TyWrapper SFuncTy
type ProcTyWrapper = TyWrapper SProcTy
type CallTyWrapper = TyWrapper SCallTy

data Const a b = Const deriving Show

liftBaseTy :: BaseTy -> TyWrapper SBaseTy (Const Void)
liftBaseTy UnitTy = TyWrap SUnit Const
liftBaseTy BoolTy = TyWrap SBool Const
liftBaseTy CharTy = TyWrap SChar Const
liftBaseTy IntTy = TyWrap SInt Const

liftVarTy :: VarTy -> VarTyWrapper (Const Void)
liftVarTy (Base ty) = case liftBaseTy ty of TyWrap sty Const -> TyWrap (SBase sty) Const
liftVarTy (Arr ty) = case liftVarTy ty of TyWrap sty Const -> TyWrap (SArr sty) Const

liftChanTy :: ChanTy -> ChanTyWrapper (Const Void)
liftChanTy (ChanInput ty) = case liftBaseTy ty of TyWrap sty Const -> TyWrap (SChanInput sty) Const
liftChanTy (ChanOutput ty) = case liftBaseTy ty of TyWrap sty Const -> TyWrap (SChanOutput sty) Const
liftChanTy (ChanBoth ty) = case liftBaseTy ty of TyWrap sty Const -> TyWrap (SChanBoth sty) Const
liftChanTy (ChanArr ty) = case liftChanTy ty of TyWrap sty Const -> TyWrap (SChanArr sty) Const

data InterpretError = InterpretError String deriving Show

type ErrorM a = Either InterpretError a

liftE :: Maybe a -> String -> ErrorM a
liftE (Just a) _ = Right a
liftE Nothing s = Left (InterpretError s)

data Context (f :: k -> *) :: [k] -> Type where
  NilC :: Context k '[]
  ConsC :: Ident -> f ty -> Context f vars -> Context f (ty ': vars)

type StoreContext = Context SStoreTy
type CallContext = Context SCallTy

data Contexts stores calls = Contexts
    { _stores :: StoreContext stores
    , _calls  :: CallContext calls
    }

deriving instance Show (StoreContext stores)
deriving instance Show (CallContext calls)
deriving instance (Show (Contexts stores calls))

addVar :: Ident -> SVarTy ty -> Contexts stores calls -> Contexts ('Var ty ': stores) calls
addVar str ty c = c { _stores = ConsC str (SVarStore ty) (_stores c) }

addChan :: Ident -> SChanTy ty -> Contexts stores calls -> Contexts ('Chan ty ': stores) calls
addChan str ty c = c { _stores = ConsC str (SChanStore ty) (_stores c) }

data ListPointer :: [k] -> k -> Type where
  Last :: ListPointer (t ': ts) t
  Prev :: ListPointer ts t -> ListPointer (t2 ': ts) t

deriving instance Show (ListPointer ks k)

contextLookup :: Context k vars -> Ident -> ErrorM (TyWrapper k (ListPointer vars))
contextLookup NilC ident = Left (InterpretError ("could not find identifier" ++ show ident))
contextLookup (ConsC var ty_marker rest) ident = if ident == var
                                            then Right (TyWrap ty_marker Last)
                                            else do TyWrap ty pos <- contextLookup rest ident
                                                    return $ TyWrap ty (Prev pos)


type family Append (list1 :: [k]) (list2 :: [k]) :: [k] where
    Append '[] list2 = list2
    Append (x ': xs) list2 = x ': (Append xs list2)

type family Map (f :: k1 -> k2) (list :: [k1]) :: [k2] where
    Map f '[] = '[]
    Map f (x ': xs) = f x ': Map f xs

type family Repeat (x :: k) (n :: Nat) :: [k] where
      Repeat x 'Zero = '[]
      Repeat x ('Succ n) = x ': Repeat x n
