{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}
module Ascend where

import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad (ap, unless, when)
import Data.Monoid ((<>))
import Data.Traversable (for)

tshow :: (Show a) => a -> Text
tshow = T.pack . show

newtype Forget a = Forget {remember :: a}
  deriving (Functor, Foldable, Traversable)

instance Eq (Forget a) where
  _ == _ = True
instance Ord (Forget a) where
  compare _ _ = EQ
instance (Show a) => Show (Forget a) where
  show (Forget a) = show a
instance Applicative Forget where
  pure = Forget
  Forget f <*> Forget x = Forget (f x)
instance Monad Forget where
  return = Forget
  Forget a >>= f = f a

type Binder = Forget Text

data Var a =
    F a
  | B Binder
  deriving (Functor, Foldable, Traversable, Eq, Ord, Show)

data Phase = Earth | Heaven
  deriving (Eq, Ord, Show)

type Type = Exp

data Exp a =
    -- Types
    Type
  | Pi Binder Phase (Type a) (Type (Var a))
    -- Values
  | Lam Binder (Exp (Var a))
    -- Neutral
  | Neutral a [Exp a]
  deriving (Functor, Foldable, Traversable, Eq, Show)

instance Applicative Exp where
  pure = return
  (<*>) = ap

(>>>=) :: (Monad f) => f (Var a) -> (a -> f b) -> f (Var b)
ma >>>= mf = ma >>= (\case
  B b -> return (B b)
  F v -> fmap F (mf v))

instance Monad Exp where
  return v = Neutral v []

  ma >>= mf = case ma of
    Type -> Type
    Pi b phase dom cod -> Pi b phase (dom >>= mf) (cod >>>= mf)
    Lam b body -> Lam b (body >>>= mf)
    Neutral v args -> app (mf v) (map (>>= mf) args)

app :: Exp a -> [Exp a] -> Exp a
app f = \case
  [] -> f
  arg : args -> case f of
    Lam _b body -> app
      (body >>= (\case
        B{} -> arg
        F v -> return v))
      args
    Neutral v args' -> Neutral v (args' ++ args)
    Type -> error "applying to a Type"
    Pi{} -> error "applying to a Pi"

type Env a = a -> (Phase, Type a)

extend :: Env a -> (Phase, Type a) -> Env (Var a)
extend env (phase, ty_) = \case
  B{} -> (phase, fmap F ty_)
  F v -> let
    (phase', ty') = env v
    in (phase', fmap F ty')

type IsVar a = (Eq a)

checkEqual :: (IsVar a) => Exp a -> Exp a -> Either Text ()
checkEqual a b = do
  unless (a == b) (Left "expressions not equal")

check ::
     (IsVar a)
  => Env a -> Type a -> Exp a -> Either Text ()
check env ty = \case
  Type -> do
    checkEqual Type ty
  Pi _b domPhase dom cod -> do
    checkEqual Type ty
    check env Type dom
    check (extend env (domPhase, dom)) Type cod
  Lam _b body -> case ty of
    Pi _b domPhase dom cod -> do
      check (extend env (domPhase, dom)) cod body
    _ -> do
      Left "non-Pi type for Lam"
  Neutral v args -> do
    let (_phase, funTy) = env v
    ty' <- checkSpine env funTy args
    checkEqual ty ty'

checkSpine ::
     (IsVar a)
  => Env a -> Type a -> [Exp a] -> Either Text (Type a)
checkSpine env ty = \case
  [] -> return ty
  arg : args -> case ty of
    Pi _b _domPhase dom cod -> do
      check env dom arg
      checkSpine
        env
        (cod >>= \case
          B{} -> arg
          F v -> return v)
        args
    _ -> Left "non-Pi type for application"

data UExp a =
    ULam Binder (UExp (Var a))
  | UNeutral a [UExp a]
  deriving (Functor, Foldable, Traversable, Eq, Show)

erase :: Env a -> Type a -> Exp a -> Either Text (UExp a)
erase env ty = \case
  Type -> Left "Type in erasure"
  Pi{} -> Left "Pi in erasure"
  Lam b body0 -> case ty of
    Pi _b domPhase dom cod -> do
      body <- erase (extend env (domPhase, dom)) cod body0
      case domPhase of
        Heaven -> do
          for body $ \case
            B{} -> Left "free var in erased body"
            F v -> return v
        Earth -> do
          return (ULam b body)
    _ -> Left "non-Pi for Lam in erasure"
  Neutral v args0 -> do
    let (phase, ty') = env v
    when (phase == Heaven) $
      Left "Heaven var in erasure"
    args <- eraseSpine env ty' args0
    return (UNeutral v args)

eraseSpine :: Env a -> Type a -> [Exp a] -> Either Text [UExp a]
eraseSpine env ty = \case
  [] -> return []
  arg0 : args0 -> case ty of
    Pi _b domPhase dom cod -> do
      args <- eraseSpine
        env
        (cod >>= (\case
          B{} -> arg0
          F v -> return v))
        args0
      case domPhase of
        Heaven -> return args
        Earth -> do
          arg <- erase env dom arg0
          return (arg : args)
    _ -> Left "non-Pi type in application and eraseSpine"


{-
checkPhase ::
     Phase -- ^ the phase we're checking against
  -> Phase -- ^ the phase we have
  -> Either Text ()
checkPhase phase1 phase2 = do
  unless (phase2 <= phase1) (Left ("illegal descent: "  <> tshow (phase1, phase2)))

check :: (IsVar a) => Env a -> Type a -> Exp a -> Either Text Phase
check env ty = \case
  Type -> do
    checkEqual ty Type
    return Heaven
  Pi _b domPhase dom cod -> do
    checkPhase Heaven =<< check env Type dom
    checkPhase Heaven =<< check (extend env (domPhase, dom)) Type cod
    return Heaven
  Lam _b body -> do
    case ty of
      Pi _b domPhase dom cod -> do
        checkPhase Heaven =<< check env Type dom
        check (extend env (domPhase, dom)) cod body
      _ -> Left "lambda without pi type"
  Neutral v args -> do
    let (vphase, vty) = env v
    (phase, ty') <- checkSpine env vphase vty args
    checkEqual ty ty'
    return phase

checkSpine ::
     (IsVar a)
  => Env a -> Phase -> Type a -> [Exp a] -> Either Text (Phase, Type a)
checkSpine = error "TODO"
-}
{-
check :: (IsVar a) => Env a -> Phase -> Type a -> Exp a -> Either Text ()
check env phase ty = \case
  Type -> do
    checkPhase phase Heaven
    checkEqual ty_ Type
  Pi _b domPhase dom cod -> do
    checkPhase phase Heaven
    checkEqual ty_ Type
    check env Heaven Type dom
    check (extend env (domPhase, dom)) phase Type cod
  Lam _b body -> do
    case ty_ of
      Pi _b domPhase dom cod -> do
        check (extend env (domPhase, dom)) phase cod body
      _ -> Left "lambda without pi type"
  Neutral v args -> do
    (phase', ty') <- infer env v args
    checkPhase phase phase'
    checkEqual ty_ ty'

infer :: Env a -> a -> [Exp a] -> Either Text (Phase, Type a)
infer env v args = do
  let (phase, ty_) = env v
  checkSpine env phase ty_ args

phaseFor :: Phase -> Phase -> Phase
phaseFor Earth Earth = Earth
phaseFor Earth Heaven = Heaven
phaseFor Heaven Earth = Heaven
phaseFor Heaven Heaven = Heaven

checkSpine :: Env a -> Phase -> Type a -> [Exp a] -> Either Text (Phase, Type a)
checkSpine = error "TODO"
-}
{-
checkSpine env phase ty = \case
  [] -> return (phase, ty)
  arg : args -> case ty of
    Pi _b domPhase dom cod -> do
      check env domPhase
-}
