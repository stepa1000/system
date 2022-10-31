{-# Language TypeOperators, TypeFamilies, FlexibleContexts
  , UndecidableInstances, ConstraintKinds, ScopedTypeVariables
  , RankNTypes, AllowAmbiguousTypes, TypeApplications, GADTs
  , MultiParamTypeClasses, DeriveGeneric, DataKinds
  , DerivingVia, BangPatterns
#-}
module Control.Core.YonedaIO where

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

import Data.Functor.Coyoneda
import Data.Functor.Yoneda

data YonedaIO s = YonedaIO s

type instance SysAdjF (YonedaIO s) = Yoneda (Coyoneda ( SysAdjF s))
type instance SysAdjG (YonedaIO s) = Yoneda (Coyoneda ( SysAdjG s))
type instance SysMonad (YonedaIO s) = SysMonad s
type instance SysComonad (YonedaIO s) = SysComonad s

type SysInterfaceM s a b = SysAdjMonad (YonedaIO s) (Either a b)
type SysInterfaceW s a b = SysAdjComonad (YonedaIO s) (Either a b)

unSysInterfaceM :: SysAdjMonad (YonedaIO s) a -> SysAdjMonad s a
unSysInterfaceM (UnSysAdjMonad sam) = undefined -- fmap (lowerCoyoneda $ lowerYoneda) $ lowerCoyoneda $ lowerYoneda sam
