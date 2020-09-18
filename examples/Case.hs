{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE Rank2Types, FlexibleContexts, UndecidableInstances, TypeFamilies #-}
{-# LANGUAGE ConstraintKinds, KindSignatures, PolyKinds, TypeOperators #-}
{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, ScopedTypeVariables #-}
{-# LANGUAGE FunctionalDependencies #-}

module Main where

import Control.Monad.IO.Class
import Data.Proxy
import Data.Monoid
import Data.Reflection
import Data.Constraint
import Data.Constraint.Unsafe

newtype Lift (p :: (* -> *) -> Constraint) f s (a :: *) =
    Lift
        { lower :: f a
        }

class ReifiableConstraint p where
    data Def (p :: (* -> *) -> Constraint) (f :: (* -> *)) :: *
    reifiedIns :: Reifies s (Def p f) :- p (Lift p f s)

reflectResult1 :: forall f s a b. Reifies s a => (a -> f s b) -> f s b
reflectResult1 f = f (reflect (Proxy :: Proxy s))

instance ReifiableConstraint Functor where
    data Def Functor f = Functor { fmap_ :: forall a b. (a -> b) -> f a -> f b }
    -- reifiedIns :: Reifies s (Def p f) :- p (Lift p f s)
    reifiedIns = Sub Dict

instance (Reifies s (Def Functor f)) =>
         Functor (Lift Functor f s) where
    fmap f (Lift fa) = reflectResult1 $ \functor -> Lift (fmap_ functor f fa)

instance (Reifies s (Def MonadIO f)) => Functor (Lift MonadIO f s) where
instance (Reifies s (Def MonadIO f)) => Applicative (Lift MonadIO f s) where
instance (Reifies s (Def MonadIO f)) => Monad (Lift MonadIO f s) where

instance ReifiableConstraint MonadIO where
    data Def MonadIO f = MonadIO { liftIO_ :: forall a . IO a -> f a }
    -- reifiedIns :: Reifies s (Def p f) :- p (Lift p f s)
    reifiedIns = Sub Dict

instance (Reifies s (Def MonadIO f)) =>
         MonadIO (Lift MonadIO f s) where
    liftIO ioa = reflectResult1 $ \monadio -> Lift (liftIO_ monadio ioa)

with ::
       Def p f
    -> (forall (s :: *). Reifies s (Def p f) => Lift p f s a)
    -> f a
with d v = reify d (asProxyOf v)

asProxyOf :: Lift p f s a -> proxy s -> f a
asProxyOf (Lift f) _ = f

using ::
       forall p f a. ReifiableConstraint p
    => Def p f
    -> (p f => f a)
    -> f a
using d m =
    reify d $ \(_ :: Proxy s) ->
        let
            replaceProof :: Reifies s (Def p f) :- p f
            replaceProof = trans proof reifiedIns
              where
                proof = unsafeCoerceConstraint :: p (Lift p f s) :- p f
         in m \\ replaceProof

data T a = T a deriving (Show)

main :: IO ()
main = do
  print $ using (Functor (\f (T a) -> (T (f a)))) (fmap (+1) (T 3))
