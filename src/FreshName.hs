{-# LANGUAGE GeneralizedNewtypeDeriving, UndecidableInstances, TypeSynonymInstances, FlexibleInstances #-}

module FreshName where

import Control.Monad.State
import Control.Monad.Identity
import Data.List((\\))

type Name = String

class Monad m => MonadNameGen m where
  fresh :: m Name

newtype NameGenT m a = NameGenT (StateT [Name] m a)
  deriving (Applicative, Functor, Monad, MonadIO, MonadTrans)

type NameGen = NameGenT Identity

runNameGen :: NameGen a -> a
runNameGen = runIdentity . runNameGenT

instance (Monad m) => MonadNameGen (NameGenT m) where
  fresh = NameGenT $ do
    t:ts <- get
    put ts
    return t

runNameGenTWithout :: (Monad m) => [Name] -> NameGenT m a -> m a
runNameGenTWithout xs (NameGenT x) =
   evalStateT x (["x" ++ (show i) | i <- [(0::Int)..]] \\ xs)

runNameGenT :: (Monad m) => NameGenT m a -> m a
runNameGenT (NameGenT x) =
   evalStateT x ["x" ++ (show i) | i <- [(0::Int)..]]
