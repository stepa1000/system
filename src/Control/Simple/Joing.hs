{-# Language TypeOperators, TypeFamilies, FlexibleContexts
  , UndecidableInstances, ConstraintKinds, ScopedTypeVariables
  , RankNTypes, AllowAmbiguousTypes, TypeApplications, GADTs
  , MultiParamTypeClasses, DeriveGeneric, DataKinds
  , DerivingVia, BangPatterns, InstanceSigs
  , FlexibleInstances
#-}
module Control.Simple.Joing where

import Prelude as Pre
import GHC.Generics
import GHC.TypeLits
import System.Random
-- import GHC.Prim

import Control.Monad.Trans.Adjoint as M
import Control.Comonad.Trans.Adjoint as W
import Control.Monad.Trans
import Control.Comonad.Trans.Class

import Control.Core.System
import Control.Core.Composition

import Control.Comonad 
import Control.Monad
import Control.Arrow as Arr

import Control.Invertible.Monoidal.Free as Inv
import Control.Monad.Free as MF
import Control.Comonad.Cofree as CF
import Control.Lens

import Control.Monad.Trans.Iter as MF
import Control.Comonad.Trans.Coiter as CFi
import Control.Comonad.Trans.Env as E
import Control.Monad.Reader as R

import Control.Comonad.Trans.Traced as E
import Control.Monad.Writer as R
import Control.Comonad.Trans.Store

import Data.Functor.Adjunction
import Data.Proxy
import Data.Function
import Data.Functor.Sum

import Data.Profunctor
import Data.Profunctor.Composition
import Data.Profunctor.Rep as PRep

import Data.Bifunctor.Functor
import Data.Functor.Rep as Adj
import Data.Functor.Yoneda

import Data.Distributive
import Data.Either
import Data.Typeable
import Data.Maybe

import Data.Bifunctor
import Data.These
import Data.Functor.Identity
import Data.Dynamic

import Data.Vector as Vec
-- import Data.Dynamic as D

import Unsafe.Coerce

import Control.Core.Postlude


{-
class ElemSysten s where
	type ElemAdjF s :: * -> *
	type ElemAdjG s :: * -> *

type family SysAdjF s :: * -> *
type family SysAdjG s :: * -> *
type family SysMonad s :: * -> *
type family SysComonad s :: * -> *
-}

data Joing a b = Joing
	{ --vectorObjJoing :: Vector a
	  joingNumObj :: Int
	, joingNumApp :: Int
	, joingFun :: Vector a -> b
	}

type JoingAdj a b = VarAdj (Joing a b)

--instance System (Joing a b) where
--type instance SysAdjF (JoingAdj a b) = ElemAdjF (JoingAdj a b)
--type instance SysAdjG (JoingAdj a b) = ElemAdjG (JoingAdj a b) 
type instance SysMonad (JoingAdj a b) = IO
type instance SysComonad (JoingAdj a b) = Store StdGen	

joingSysM :: (Typeable a, Typeable b) => Proxy b -> Vector a -> SysAdjMonad (JoingAdj a b) b
joingSysM (Proxy :: Proxy b) (va :: Vector a) = do
	j <- getEnvSysAdjM (Proxy @(Joing a b))
	li <- liftSysM $ fio j
	return $ (joingFun j) (Vec.fromList $ fmap (\i-> va ! i) li)
	where
		fio :: Joing a b -> IO [Int]
		fio j = do
			s <- initStdGen
			return $ Pre.take (joingNumApp j) $ randomRs (0,joingNumObj j) s	

joingSysMN :: (Typeable a, Typeable b) => Proxy b -> Int -> Vector a -> SysAdjMonad (JoingAdj a b) [b]
joingSysMN p i v = R.mapM (const $ joingSysM p v) [0..i]

jointSysW :: (Typeable a, Typeable b) => SysAdjComonad (JoingAdj a b) (Vector a) -> SysAdjComonad (JoingAdj a b) b
jointSysW s = (\b-> fmap (const b) $ (mapSysW (seeks (snd . next)) s )) $ 
	(joingFun j) $ fmap (\i-> (extract s) ! i) $ 
	Vec.fromList $ Pre.take (joingNumApp j) $ fst $
	experiment (\g->(\n->(n,g)) $ randomRs (0, joingNumObj j) g) $ lowerSysW s
	where
		j = getEnvSysAdjW s
