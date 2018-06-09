{-# language DeriveFunctor         #-}
{-# language FlexibleContexts      #-}
{-# language FlexibleInstances     #-}
{-# language GADTs                 #-}
{-# language KindSignatures        #-}
{-# language LambdaCase            #-}
{-# language MultiParamTypeClasses #-}
{-# language PatternSynonyms       #-}
{-# language Rank2Types            #-}
{-# language ScopedTypeVariables   #-}
{-# language TypeOperators         #-}
{-# language UndecidableInstances  #-}
module Main where

import Data.Functor.Const

import Kit
import HKit

data IntVal (e :: * -> *) l = IntVal Int
  deriving Functor

instance HFunctor IntVal where
  hmap _ (IntVal a) = (IntVal a)

data Arith (e :: * -> *) l where
  Add :: e Int -> e Int -> Arith e Int
  Sub :: e Int -> e Int -> Arith e Int
  Mul :: e Int -> e Int -> Arith e Int
  Div :: e Int -> e Int -> Arith e Int

instance HFunctor Arith where
  hmap trans = \case
    Add x y -> Add (trans x) (trans y)
    Sub x y -> Sub (trans x) (trans y)
    Mul x y -> Mul (trans x) (trans y)
    Div x y -> Div (trans x) (trans y)

instance (IntVal :<: f, Arith :<: f) => Num (Term f Int) where
  x + y       = inject (Add x y)
  x - y       = inject (Sub x y)
  x * y       = inject (Mul x y)
  negate x    = 0 - x
  abs         = undefined
  signum      = undefined
  fromInteger = inject . IntVal . fromInteger

data Logic (e :: * -> *) l where
  And :: e Bool -> e Bool -> Logic e Bool
  Or  :: e Bool -> e Bool -> Logic e Bool
  Not :: e Bool           -> Logic e Bool

instance HFunctor Logic where
  hmap trans = \case
    And x y -> And (trans x) (trans y)
    Or  x y -> Or  (trans x) (trans y)
    Not x   -> Not (trans x)

data Comparison (e :: * -> *) l where
  Eq  :: e l -> e l -> Comparison e Bool
  Neq :: e l -> e l -> Comparison e Bool

instance HFunctor Comparison where
  hmap trans = \case
    Eq x y  -> Eq (trans x) (trans y)
    Neq x y -> Neq (trans x) (trans y)


class Eval e v where
  evalAlgebra :: Alg e v

eval :: (HFunctor e, Eval e v) => Term e ~> v
eval = cata' evalAlgebra

-- Not used but potentially useful:
-- class EvalI f where
--   evalAlgI :: Alg f Identity

-- evalI :: (EvalI f, HFunctor f) => Term f t -> t
-- evalI = runIdentity . cata' evalAlgI

instance Eval IntVal (Const Int) where
  evalAlgebra (IntVal i) = (Const i)

instance Eval Arith (Const Int) where
  evalAlgebra = \case
    Add x y -> x + y
    Sub x y -> x - y
    Mul x y -> x * y
    Div _x _y -> error "TODO" -- x `div` y

instance Eval Logic (Const Bool) where
  evalAlgebra = \case
    And x y -> Const (getConst x && getConst y)
    Or  x y -> Const (getConst x || getConst y)
    Not x   -> Const (not (getConst x))

instance Eval Comparison (Const Bool) where
  evalAlgebra = \case
    Eq  x y -> Const (x == y)
    Neq x y -> Const (x /= y)

instance (Eval f a, Eval g a) => Eval (f :+: g) a where
  evalAlgebra = \case
    Inl x -> evalAlgebra x
    Inr y -> evalAlgebra y


class Render f where
  rendersPrec :: Int -> Alg f (Const ShowS)
  -- rendersPrec :: Int -> forall a. Show a => f (Const ShowS) a -> Const ShowS a

instance Render IntVal where
  rendersPrec prec (IntVal i) = Const (showsPrec prec i)

instance Render Arith where
  -- TODO: wrong precedence
  rendersPrec prec = Const . showParen (prec > 10) . \case
    Add x y -> getConst x . showString " + " . getConst y
    Sub x y -> getConst x . showString " - " . getConst y
    Mul x y -> getConst x . showString " * " . getConst y
    Div x y -> getConst x . showString " / " . getConst y

instance Render Logic where
  -- TODO: wrong precedence
  rendersPrec prec = Const . showParen (prec > 10) . \case
    And x y -> getConst x . showString " && " . getConst y
    Or  x y -> getConst x . showString " || " . getConst y
    Not x   ->              showString "not " . getConst x

instance Render Comparison where
  -- TODO: wrong precedence
  rendersPrec prec = Const . showParen (prec > 10) . \case
    Eq  x y -> getConst x . showString " == " . getConst y
    Neq x y -> getConst x . showString " != " . getConst y

instance (Render f, Render g) => Render (f :+: g) where
  rendersPrec prec = Const . showParen (prec > 10) . getConst . \case
    Inl x -> rendersPrec 11 x
    Inr y -> rendersPrec 11 y

pretty :: forall f l. (HFunctor f, Render f, Show l) => Term f l -> String
pretty t = getConst (cata' (rendersPrec 10) t) ""

showIt :: (HFunctor f, Render f, Eval f (Const Int)) => Term f Int -> IO ()
showIt expr = do
  putStrLn (pretty expr)
  putStrLn "-->"
  print (getConst (eval expr :: Const Int Int))
  putStrLn "\n"

main :: IO ()
main = do
  showIt $
    let addExample :: Term (IntVal :+: Arith) Int
        addExample = 118 + 1219
    in addExample

  showIt $
    let x :: Term (Arith :+: IntVal) Int
        x = 30000 + 1330 + 7
    in x

  showIt $
    let x :: Term (IntVal :+: Arith) Int
        x = 80 * 5 + 4
    in x

  let x :: Term (Comparison :+: IntVal :+: Arith) Bool
      x = Term (Inl (Eq (80 * 5 :: Term (Comparison :+: IntVal :+: Arith) Int) 4))
  putStrLn (pretty x)
  -- print (getConst (eval x :: Const Bool Bool))
