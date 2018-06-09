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
import Data.Functor.Identity

import Kit
import HKit

data SimpleVal (e :: * -> *) l = SimpleVal l
  deriving Functor

instance HFunctor SimpleVal where
  hmap _ (SimpleVal a) = (SimpleVal a)

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

instance (SimpleVal :<: f, Arith :<: f) => Num (Term f Int) where
  x + y       = inject (Add x y)
  x - y       = inject (Sub x y)
  x * y       = inject (Mul x y)
  negate x    = 0 - x
  abs         = undefined
  signum      = undefined
  fromInteger = inject . SimpleVal . fromInteger


class Eval e v where
  evalAlgebra :: Alg e (Term v)

eval :: (HFunctor e, Eval e v) => Term e ~> Term v
eval = cata' evalAlgebra

-- Not used but potentially useful:
class EvalI f where
  evalAlgI :: Alg f Identity

evalI :: (EvalI f, HFunctor f) => Term f t -> t
evalI = runIdentity . cata' evalAlgI

instance SimpleVal :<: v => Eval SimpleVal v where
  evalAlgebra = inject

instance (Arith :<: v, SimpleVal :<: v) => Eval Arith v where
  evalAlgebra = \case
    Add x y -> x + y
    Sub x y -> x - y
    Mul x y -> x * y
    Div _x _y -> error "TODO" -- x `div` y

instance (Eval f a, Eval g a) => Eval (f :+: g) a where
  evalAlgebra = \case
    Inl x -> evalAlgebra x
    Inr y -> evalAlgebra y


class Render f where
  -- rendersPrec :: Int -> Alg f (Const ShowS)
  rendersPrec :: Int -> forall a. Show a => f (Const ShowS) a -> Const ShowS a

instance Render SimpleVal where
  rendersPrec prec (SimpleVal i) = Const (showsPrec prec i)

instance Render Arith where
  rendersPrec prec = Const . showParen (prec > 10) . \case
    Add x y -> go x . showString " + " . go y
    Sub x y -> go x . showString " - " . go y
    Mul x y -> go x . showString " * " . go y
    Div x y -> go x . showString " / " . go y
    where go = getConst

instance (Render f, Render g) => Render (f :+: g) where
  rendersPrec prec = Const . showParen (prec > 10) . getConst . \case
    Inl x -> rendersPrec 11 x
    Inr y -> rendersPrec 11 y

pretty :: forall f l. (HFunctor f, Render f, Show l) => Term f l -> String
pretty t = getConst (cata'' (rendersPrec 10) t) ""
  where
  cata'' :: forall g a. (forall b. f g b -> g b) -> Term f a -> g a
  cata'' f = run
    where run :: forall b. Term f b -> g b
          run (Term t) = f (hmap run t)

showIt :: (HFunctor f, Render f) => Term f Int -> IO ()
showIt expr = do
  putStrLn (pretty expr)
  -- putStrLn "-->"
  -- putStrLn (pretty (eval expr))
  putStrLn "\n"

main :: IO ()
main = do
  putStrLn "here"

  let addExample :: Term (SimpleVal :+: Arith) Int
      addExample = 118 + 1219

  showIt addExample

--   showIt $
--     let x :: Term (Sum Arith SimpleVal) Int
--         x = 30000 + 1330 + 7
--     in x

--   showIt $
--     let x :: Term (Sum SimpleVal Arith) Int
--         x = 80 * 5 + 4
--     in x
