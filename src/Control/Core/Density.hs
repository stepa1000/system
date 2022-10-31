{-# Language TypeOperators, TypeFamilies, FlexibleContexts
  , UndecidableInstances, ConstraintKinds, ScopedTypeVariables
  , RankNTypes, AllowAmbiguousTypes, TypeApplications, GADTs
  , MultiParamTypeClasses, DeriveGeneric, DataKinds
  , DerivingVia, BangPatterns
#-}
module Control.Core.Density where

import GHC.Generics
import GHC.TypeLits
-- import GHC.Prim

import Control.Monad.Trans.Adjoint as M
import Control.Comonad.Trans.Adjoint as W
import Control.Monad.Trans
import Control.Comonad.Trans.Class

import Control.Core.System
import Control.Core.Composition

import Control.Comonad 
import Control.Monad
import Control.Arrow

import Control.Invertible.Monoidal.Free as Inv
import Control.Monad.Free as MF
import Control.Comonad.Cofree as CF

import Data.Functor.Adjunction
import Data.Proxy
import Data.Function
import Data.Functor.Sum

import Data.Profunctor
import Data.Profunctor.Composition
import Data.Bifunctor.Functor
import Data.Functor.Rep as Adj

import Data.Distributive
import Data.Either
import Data.Typeable
import Data.Maybe

import Data.Bifunctor
import Data.These
import Data.Functor.Identity
import Unsafe.Coerce
{-
data (:^^:) a b = Powsition a b

type instance SysAdjF (s1 :^^: s2) = SysAdjF s2
type instance SysAdjG (s1 :^^: s2) = SysAdjG s2
type instance SysMonad (s1 :^^: s2) = SysAdjMonad s1 :*: SysMonad s2
type instance SysComonad (s1 :^^: s2) = Sum (SysAdjComonad s1) (SysComonad s2)
-}


