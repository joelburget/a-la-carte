{-# language DeriveFunctor         #-}
{-# language FlexibleContexts      #-}
{-# language FlexibleInstances     #-}
{-# language LambdaCase            #-}
{-# language MultiParamTypeClasses #-}
{-# language PatternSynonyms       #-}
{-# language Rank2Types            #-}
{-# language TypeOperators         #-}
module Main where

import Control.Lens
import Control.Monad.Free
import Data.Functor.Foldable
import Data.Functor.Sum

import Kit

data Val e = Val Int
  deriving Functor

data Add e = Add e e
  deriving Functor

data Mul x = Mul x x
  deriving Functor

val :: (Val :<: f) => Int -> Fix f
val x = injectFix (Val x)

infixl 6 .+
(.+) :: (Add :<: f) => Fix f -> Fix f -> Fix f
x .+ y = injectFix (Add x y)

infixl 7 .*
(.*) :: (Mul :<: f) => Fix f -> Fix f -> Fix f
x .* y = injectFix (Mul x y)

match :: (g :<: f) => Fix f -> Maybe (g (Fix f))
match (Fix t) = preview inj t

distr :: (Add :<: f, Mul :<: f) => Fix f -> Maybe (Fix f)
distr t = do
  Mul a b <- match t
  Add c d <- match b
  pure (a .* c .+ a .* d)

data Incr t = Incr Int t
  deriving Functor

data Recall t = Recall (Int -> t)
  deriving Functor

data Clear t = Clear

incr :: (Incr :<: f) => Int -> Free f ()
incr i = injectFree (Incr i (Pure ()))

recall :: (Recall :<: f) => Free f Int
recall = injectFree (Recall Pure)

tick :: Free (Recall :+: Incr) Int
tick = do
  y <- recall
  incr 1
  return y

clear :: (Clear :<: f) => Free f ()
clear = injectFree Clear

newtype Mem = Mem Int
  deriving Show


class Functor f => Run f where
  runAlgebra :: f (Mem -> (a, Mem)) -> (Mem -> (a, Mem))

instance Run Incr where
  runAlgebra (Incr k r) (Mem i) = r (Mem (i + k))

instance Run Recall where
  runAlgebra (Recall r) (Mem i) = r i (Mem i)

instance (Run f, Run g) => Run (f :+: g) where
  runAlgebra (InL f) = runAlgebra f
  runAlgebra (InR g) = runAlgebra g

run :: Run f => Free f a -> Mem -> (a, Mem)
run = foldTerm (,) runAlgebra


class Functor f => Eval f where
  evalAlgebra :: f Int -> Int

instance Eval Val where
  evalAlgebra (Val i) = i

instance Eval Add where
  evalAlgebra (Add x y) = x + y

instance Eval Mul where
  evalAlgebra (Mul x y) = x * y

instance (Eval f, Eval g) => Eval (f :+: g) where
  evalAlgebra (InL x) = evalAlgebra x
  evalAlgebra (InR y) = evalAlgebra y

eval :: Eval f => Fix f -> Int
eval expr = foldExpr evalAlgebra expr


class Render f where
  render :: Render g => f (Fix g) -> String

instance Render Val where
  render (Val i) = show i

instance Render Add where
  render (Add x y) = "(" ++ pretty x ++ " + " ++ pretty y ++ ")"

instance Render Mul where
  render (Mul x y) = "(" ++ pretty x ++ " * " ++ pretty y ++ ")"

instance (Render f, Render g) => Render (f :+: g) where
  render (InL x) = render x
  render (InR y) = render y

pretty :: Render f => Fix f -> String
pretty (Fix t) = render t


main :: IO ()
main = do

  let showIt :: (Render f, Eval f) => Fix f -> IO ()
      showIt expr = do
        putStrLn (pretty expr)
        putStrLn "-->"
        print (eval expr)
        putStrLn "\n"

      distrIt :: (Render f, Eval f, Add :<: f, Mul :<: f) => Fix f -> IO ()
      distrIt expr = do
        putStrLn (pretty expr)
        putStrLn "==>"
        print $ pretty <$> distr expr
        putStrLn "\n"

      addExample :: Fix (Val :+: Add)
      addExample = val 118 .+ val 1219

  showIt addExample
  showIt $
    let x :: Fix (Add :+: Val)
        x = val 30000 .+ val 1330 .+ val 7
    in x

  showIt $
    let x :: Fix (Val :+: Add :+: Mul)
        x = val 80 .* val 5 .+ val 4
    in x

  distrIt $
    let x :: Fix (Val :+: Add :+: Mul)
        x = val 80 .* (val 5 .+ val 4)
    in x

  print $ run tick (Mem 4)
  print $ run (incr 1 :: Free Incr ()) (Mem 8)
  print $ run (incr 1 :: Free Incr ()) (Mem 10)
