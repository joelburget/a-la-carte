{-# language DeriveFunctor         #-}
{-# language FlexibleContexts      #-}
{-# language FlexibleInstances     #-}
{-# language LambdaCase            #-}
{-# language MultiParamTypeClasses #-}
{-# language PatternSynonyms       #-}
{-# language Rank2Types            #-}
{-# language TypeOperators         #-}
{-# language UndecidableInstances  #-}
module Main where

import Control.Lens
import Data.Functor.Foldable
import Data.Functor.Sum

import Kit

data Val e = Val Int
  deriving Functor

data Arith e
  = Add e e
  | Sub e e
  | Mul e e
  | Div e e
  deriving Functor

instance (Val :<: f, Arith :<: f) => Num (Fix f) where
  x + y       = injectFix (Add x y)
  x - y       = injectFix (Sub x y)
  x * y       = injectFix (Mul x y)
  negate x    = 0 - x
  abs         = undefined
  signum      = undefined
  fromInteger = injectFix . Val . fromInteger

match :: (g :<: f) => Fix f -> Maybe (g (Fix f))
match (Fix t) = preview inj t

distr :: (Val :<: f, Arith :<: f) => Fix f -> Maybe (Fix f)
distr t = do
  Mul a b <- match t
  Add c d <- match b
  pure (a * c + a * d)

data Recall t = Recall (Int -> t)
  deriving Functor


class Functor f => Eval f where
  evalAlgebra :: f Int -> Int

instance Eval Val where
  evalAlgebra (Val i) = i

instance Eval Arith where
  evalAlgebra = \case
    Add x y -> x + y
    Sub x y -> x - y
    Mul x y -> x * y
    Div x y -> x `div` y

instance (Eval f, Eval g) => Eval (f :+: g) where
  evalAlgebra = \case
    InL x -> evalAlgebra x
    InR y -> evalAlgebra y

eval :: Eval f => Fix f -> Int
eval expr = foldExpr evalAlgebra expr


class Render f where
  renderPrec :: Render g => Int -> f (Fix g) -> ShowS

instance Render Val where
  renderPrec prec (Val i) = showsPrec prec i

instance Render Arith where
  renderPrec prec = showParen (prec > 10) . \case
    Add x y -> go x . showString " + " . go y
    Sub x y -> go x . showString " - " . go y
    Mul x y -> go x . showString " * " . go y
    Div x y -> go x . showString " / " . go y
    where go (Fix t) = renderPrec 11 t

instance (Render f, Render g) => Render (f :+: g) where
  renderPrec prec = showParen (prec > 10) . \case
    InL x -> renderPrec 11 x
    InR y -> renderPrec 11 y

pretty :: Render f => Fix f -> String
pretty (Fix t) = renderPrec 10 t ""


main :: IO ()
main = do

  let showIt :: (Render f, Eval f) => Fix f -> IO ()
      showIt expr = do
        putStrLn (pretty expr)
        putStrLn "-->"
        print (eval expr)
        putStrLn "\n"

      distrIt :: (Render f, Eval f, Arith :<: f, Val :<: f) => Fix f -> IO ()
      distrIt expr = do
        putStrLn (pretty expr)
        putStrLn "==>"
        print $ pretty <$> distr expr
        putStrLn "\n"

      addExample :: Fix (Val :+: Arith)
      addExample = 118 + 1219

  showIt addExample
  showIt $
    let x :: Fix (Arith :+: Val)
        x = 30000 + 1330 + 7
    in x

  showIt $
    let x :: Fix (Val :+: Arith)
        x = 80 * 5 + 4
    in x

  distrIt $
    let x :: Fix (Val :+: Arith)
        x = 80 * (5 + 4)
    in x
