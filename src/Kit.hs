{-# language DeriveFunctor         #-}
{-# language FlexibleContexts      #-}
{-# language FlexibleInstances     #-}
{-# language LambdaCase            #-}
{-# language MultiParamTypeClasses #-}
{-# language PatternSynonyms       #-}
{-# language Rank2Types            #-}
{-# language TypeOperators         #-}
module Kit where

import Control.Lens
import Control.Monad.Free
import Data.Functor.Foldable
import Data.Functor.Sum

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

type Injection sup sub = forall a. Prism' (sup a) (sub a)

class (Functor sub, Functor sup) => sub :<: sup where
  inj :: Injection sup sub

instance Functor f => f :<: f where
  inj = id

instance {-# OVERLAPPABLE #-} (Functor f, Functor g) => f :<: (f :+: g) where
  inj = _InL . inj

instance {-# OVERLAPS #-} (Functor f, Functor g, Functor h, f :<: g) => f :<: (h :+: g) where
  inj = _InR . inj

-- Natural transformation from @f@ to @g@
type f ~> g = forall a. f a -> g a
infixr 4 ~>

-- Natural transformation from @f@ to @Free g@
type f ~< g = f ~> Free g
infixr 4 ~<

inject :: (f :<: g) => f ~> g
inject = review inj

-- called @inject@ in DTalC
injectFix :: (f :<: g) => f (Fix g) -> Fix g
injectFix = Fix . inject

-- also called @inject@ in DTalC
injectFree :: (g :<: f) => g (Free f a) -> Free f a
injectFree = Free . inject

-- Creates a Free program from the provided injectable instruction
instruction :: (f :<: g) => f ~< g
instruction = liftF . inject

foldTerm :: Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
foldTerm pure' _imp (Pure x) = pure' x
foldTerm pure' imp (Free t)  = imp (fmap (foldTerm pure' imp) t)
