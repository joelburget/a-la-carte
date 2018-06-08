{-# language DeriveFunctor         #-}
{-# language FlexibleContexts      #-}
{-# language FlexibleInstances     #-}
{-# language LambdaCase            #-}
{-# language MultiParamTypeClasses #-}
{-# language Rank2Types            #-}
{-# language TypeOperators         #-}
module Main where

import Control.Lens
import Control.Monad.Free
import Data.Functor.Foldable
import Data.Functor.Sum

data Val e = Val Int
  deriving Functor
type IntExpr = Fix Val

data Add e = Add e e
  deriving Functor
type AddExpr = Fix Add

infixr :+:
type (:+:) = Sum

_InL :: Prism' (Sum f g a) (f a)
_InL = prism' InL $ \case
  InL x -> Just x
  InR _ -> Nothing

_InR :: Prism' (Sum f g a) (g a)
_InR = prism' InR $ \case
  InL _ -> Nothing
  InR x -> Just x

foldExpr :: Functor f => (f a -> a) -> Fix f -> a
foldExpr f (Fix t) = f (fmap (foldExpr f) t)

class Functor f => Eval f where
  evalAlgebra :: f Int -> Int

instance Eval Val where
  evalAlgebra (Val i) = i

instance Eval Add where
  evalAlgebra (Add x y) = x + y

instance (Eval f, Eval g) => Eval (f :+: g) where
  evalAlgebra (InL x) = evalAlgebra x
  evalAlgebra (InR y) = evalAlgebra y

eval :: Eval f => Fix f -> Int
eval expr = foldExpr evalAlgebra expr

type Injection sup sub = forall a. Prism' (sup a) (sub a)

class (Functor sub, Functor sup) => sub :<: sup where
  inj :: Injection sup sub

instance Functor f => f :<: f where
  inj = id

instance {-# OVERLAPPABLE #-} (Functor f, Functor g) => f :<: (f :+: g) where
  inj = _InL . inj

instance {-# OVERLAPS #-} (Functor f, Functor g, Functor h, f :<: g) => f :<: (h :+: g) where
  inj = _InR . inj

type f ~> g = forall a. f a -> g a
infixr 4 ~>

inject :: (f :<: g) => f ~> g
inject = review inj

-- called @inject@ in DTalC
injectFix :: (f :<: g) => f (Fix g) -> Fix g
injectFix = Fix . inject

val :: (Val :<: f) => Int -> Fix f
val x = injectFix (Val x)

infixl 6 .+
(.+) :: (Add :<: f) => Fix f -> Fix f -> Fix f
x .+ y = injectFix (Add x y)

addExample :: Fix (Val :+: Add)
addExample = Fix (InR (Add (Fix (InL (Val 118))) (Fix (InL (Val 1219)))))

data Mul x = Mul x x
  deriving Functor

instance Eval Mul where
  evalAlgebra (Mul x y) = x * y

infixl 7 .*
(.*) :: (Mul :<: f) => Fix f -> Fix f -> Fix f
x .* y = injectFix (Mul x y)

class Render f where
  render :: Render g => f (Fix g) -> String

pretty :: Render f => Fix f -> String
pretty (Fix t) = render t

instance Render Val where
  render (Val i) = show i

instance Render Add where
  render (Add x y) = "(" ++ pretty x ++ " + " ++ pretty y ++ ")"

instance Render Mul where
  render (Mul x y) = "(" ++ pretty x ++ " * " ++ pretty y ++ ")"

instance (Render f, Render g) => Render (f :+: g) where
  render (InL x) = render x
  render (InR y) = render y

match :: (g :<: f) => Fix f -> Maybe (g (Fix f))
match (Fix t) = preview inj t

distr :: (Add :<: f, Mul :<: f) => Fix f -> Maybe (Fix f)
distr t = do
  Mul a b <- match t
  Add c d <- match b
  pure (a .* c .+ a .* d)

showIt :: (Render f, Eval f) => Fix f -> IO ()
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

data Zero a              deriving Functor
data One a = One         deriving Functor
data Const e a = Const e deriving Functor

data Incr t = Incr Int t
  deriving Functor

data Recall t = Recall (Int -> t)
  deriving Functor

data Clear t = Clear

type f ~< g = f ~> Free g
infixr 4 ~<

-- also called @inject@ in DTalC
injectFree :: (g :<: f) => g (Free f a) -> Free f a
injectFree = Free . inject

-- Creates a Free program from the provided injectable instruction
instruction :: (f :<: g) => f ~< g
instruction = liftF . inject

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

foldTerm :: Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
foldTerm pure' _imp (Pure x) = pure' x
foldTerm pure' imp (Free t) = imp (fmap (foldTerm pure' imp) t)

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



main :: IO ()
main = do
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
