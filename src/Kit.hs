{-# language DeriveFunctor         #-}
{-# language FlexibleContexts      #-}
{-# language FlexibleInstances     #-}
{-# language KindSignatures        #-}
{-# language LambdaCase            #-}
{-# language MultiParamTypeClasses #-}
{-# language PatternSynonyms       #-}
{-# language Rank2Types            #-}
{-# language ScopedTypeVariables   #-}
{-# language TypeOperators         #-}
module Kit where

import Control.Lens
import Control.Monad.Free
import Data.Functor.Foldable
import Data.Functor.Sum

import HKit

infixr :+:
data (f :+: g) (a :: * -> *) l = Inl (f a l) | Inr (g a l)

instance (HFunctor f, HFunctor g) => HFunctor (f :+: g) where
  hmap f (Inl x) = Inl (hmap f x)
  hmap f (Inr x) = Inr (hmap f x)

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

type NatM m f g = forall i. f i -> m (g i)

class (f :: (* -> *) -> * -> *) :<: g where
  inj :: f a ~> g a
  prj :: NatM Maybe (g a) (f a)

instance HFunctor f => f :<: f where
  inj = id
  prj = Just

instance {-# OVERLAPPABLE #-} (HFunctor f, HFunctor g) => f :<: (f :+: g) where
  inj = Inl . inj
  prj = \case
    Inl x -> Just x
    Inr _ -> Nothing

instance {-# OVERLAPS #-} (HFunctor f, HFunctor g, HFunctor h, f :<: g) => f :<: (h :+: g) where
  inj = Inr . inj
  prj = \case
    Inl _ -> Nothing
    Inr x -> prj x

-- Natural transformation from @f@ to @Free g@
type f ~< g = f ~> Free g
infixr 4 ~<

type Alg f a = f a ~> a

data Term f l = Term (f (Term f) l)

-- TODO: is this the same as @cata@?
cata' :: forall f a. HFunctor f => Alg f a -> Term f ~> a
cata' f = run
  where run :: Term f ~> a
        run (Term t) = f (hmap run t)

inject :: (g :<: f) => g (Term f) ~> Term f
inject = Term . inj

-- match :: (f :<: g) => Fix g -> Maybe (f (Fix g))
-- match (Fix t) = preview inj t

-- -- called @inject@ in DTalC
-- injectFix :: (f :<: g) => f (Fix g) -> Fix g
-- injectFix = Fix . inject

-- -- also called @inject@ in DTalC
-- injectFree :: (g :<: f) => g (Free f a) -> Free f a
-- injectFree = Free . inject

-- -- Creates a Free program from the provided injectable instruction
-- instruction :: (f :<: g) => f ~< g
-- instruction = liftF . inject

foldTerm :: Functor f => (a -> b) -> (f b -> b) -> Free f a -> b
foldTerm pure' _imp (Pure x) = pure' x
foldTerm pure' imp (Free t)  = imp (fmap (foldTerm pure' imp) t)
