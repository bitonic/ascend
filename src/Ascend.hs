{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
module Ascend where

import Data.Text (Text)
import qualified Data.Text as T
import Control.Monad (ap, unless, when)
import Data.Traversable (for)
import Data.Void (Void, absurd)
import Data.String (IsString(fromString))

newtype Forget a = Forget {remember :: a}
  deriving (Functor, Foldable, Traversable, IsString)

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

checkEqual :: (IsVar a) => Exp a -> Exp a -> Either String ()
checkEqual a b = do
  unless (a == b) (Left "expressions not equal")

checkPhase :: Phase -> Phase -> Either String ()
checkPhase required given = do
  unless (given <= required) $
    Left ("Bad phase: " ++ show (required, given))

check ::
     (IsVar a)
  => Env a -> Phase -> Type a -> Exp a -> Either String ()
check env phase ty = \case
  Type -> do
    checkPhase phase Heaven
    checkEqual Type ty
  Pi _b domPhase dom cod -> do
    checkPhase phase Heaven
    checkEqual Type ty
    check env Heaven Type dom
    check (extend env (domPhase, dom)) Heaven Type cod
  Lam _b body -> case ty of
    Pi _b domPhase dom cod -> do
      check (extend env (domPhase, dom)) phase cod body
    _ -> do
      Left "non-Pi type for Lam"
  Neutral v args -> do
    let (phase', funTy) = env v
    checkPhase phase phase'
    ty' <- checkSpine env phase funTy args
    checkEqual ty ty'

lub :: Phase -> Phase -> Phase
lub a b = case (a, b) of
  (Earth, Earth) -> Earth
  (Heaven, Earth) -> Heaven
  (Earth, Heaven) -> Heaven
  (Heaven, Heaven) -> Heaven

checkSpine ::
     (IsVar a)
  => Env a -> Phase -> Type a -> [Exp a] -> Either String (Type a)
checkSpine env phase ty = \case
  [] -> return ty
  arg : args -> case ty of
    Pi _b domPhase dom cod -> do
      check env (lub phase domPhase) dom arg
      checkSpine
        env
        phase
        (cod >>= \case
          B{} -> arg
          F v -> return v)
        args
    _ -> Left "non-Pi type for application"

data UExp a =
    ULam Binder (UExp (Var a))
  | UNeutral a [UExp a]
  deriving (Functor, Foldable, Traversable, Eq, Show)

erase :: Env a -> Type a -> Exp a -> Either String (UExp a)
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

eraseSpine :: Env a -> Type a -> [Exp a] -> Either String [UExp a]
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

-- DSL
-- --------------------------------------------------------------------

abstract :: (Functor f, Eq a) => a -> Binder -> f a -> f (Var a)
abstract v b = fmap (\v' -> if v == v' then B b else F v')

ety :: Exp a
ety = Type

(==>) :: (String, Phase, Type String) -> Type String -> Type String
(v, phase, dom) ==> cod = Pi b phase dom (abstract v b cod)
  where
    b = Forget (T.pack v)

(-->) :: (Phase, Type String) -> Type String -> Type String
(phase, dom) --> cod = Pi "" phase dom (fmap F cod)

elam :: String -> Exp String -> Exp String
elam v body = Lam b (abstract v b body)
  where
    b = Forget (T.pack v)

eapp :: String -> [Exp String] -> Exp String
eapp = Neutral

ev :: String -> Exp String
ev v = Neutral v []

instance IsString (Exp String) where
  fromString = ev

test :: String -> [(String, Phase, Type String)] -> Phase -> Type String -> Exp String -> IO ()
test name vars00 phase ty0 e0 = do
  let mbErr =
        go (\v -> Left ("out of scope var " ++ show v)) absurd vars00 $ \getv env -> do
          ty <- traverse getv ty0
          e <- traverse getv e0
          check env phase ty e
  putStrLn ("### " ++ name)
  case mbErr of
    Left err -> do
      putStrLn "ERROR"
      putStrLn err
    Right () -> putStrLn "OK"
  where
    go ::
         (IsVar a)
      => (String -> Either String a)
      -> Env a
      -> [(String, Phase, Type String)]
      -> (forall b. (IsVar b) => (String -> Either String b) -> Env b -> Either String c)
      -> Either String c
    go getv env vars0 cont = case vars0 of
      [] -> cont getv env
      (v, tyPhase, ty) : vars -> do
        ty' <- traverse getv ty
        go
          (\v' -> if v == v'
              then return (B (Forget (T.pack v)))
              else F <$> getv v')
          (extend env (tyPhase, ty'))
          vars
          cont

test1 :: IO ()
test1 = test "SIMPLE-APP"
  [ ("Bool", Heaven, Type)
  , ("true", Earth, "Bool")
  , ("false", Earth, "Bool")
  , ("not", Earth, (Earth, "Bool") --> ev "Bool")
  ]
  Earth
  "Bool"
  (eapp "not" ["true"])

test2 :: IO ()
test2 = test "NAT"
  [ ("Nat", Heaven, Type)
  , ("zero", Earth, "Nat")
  , ("suc", Earth, (Earth, "Nat") --> "Nat")
  , ("n", Heaven, "Nat")
  ]
  Heaven
  "Nat"
  (eapp "suc" ["n"])

test3 :: IO ()
test3 = test "SHOULD-FAIL"
  [ ("Nat", Heaven, Type)
  , ("zero", Earth, "Nat")
  , ("suc", Earth, (Earth, "Nat") --> "Nat")
  , ("n", Heaven, "Nat")
  ]
  Earth
  "Nat"
  "n"

main :: IO ()
main = do
  test1
  test2
  test3
