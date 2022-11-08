{-# Language RankNTypes, ScopedTypeVariables, DataKinds, TypeOperators
 , TypeFamilies, ConstraintKinds, FlexibleContexts, DeriveAnyClass 
 , DeriveFunctor, DerivingVia, UndecidableInstances, PatternSynonyms #-}

module Control.Core.System where

import GHC.Generics

import Data.Functor.Adjunction
import Data.Profunctor
import Data.Profunctor.Composition
import Data.Profunctor.Choice

import Data.Proxy
import Data.Invertible.Bijection
import Data.Functor.Kan.Lan
import Data.Functor.Kan.Ran

import Control.Comonad
import Control.Arrow
import Control.Monad.Trans.Adjoint as M
import Control.Comonad.Trans.Adjoint as W

import Control.Monad.Trans as M
import Control.Comonad.Trans.Class as W
import Control.Monad.Codensity
import Control.Comonad.Density

import qualified Control.Category as C
import Control.Applicative
import Control.Invertible.Monoidal.Free as Inv

-- Class system

type CxtSystemCore s = 
  ( Adjunction (SysAdjF s) (SysAdjG s)
  , Monad (SysMonad s)
  , Comonad (SysComonad s)
  -- , System s
  )

--class CxtSystemCore s =>  SystemCore s where
-- class System s where
type family SysAdjF s :: * -> *
type family SysAdjG s :: * -> *
type family SysMonad s :: * -> *
type family SysComonad s :: * -> *
--  sysProxy :: Proxy s 

--                                      Types system

-- Monad and Comonad

data SysAdjMonad s x = SysAdjMonad {unSysAdjMonad :: M.AdjointT (SysAdjF s) (SysAdjG s) (SysMonad s) x}
data SysAdjComonad s x = SysAdjComonad {unSysAdjComonad :: W.AdjointT (SysAdjF s) (SysAdjG s) (SysComonad s) x}

runSysAdjMonad :: SysAdjMonad s x -> SysAdjG s (SysMonad s (SysAdjF s x))
runSysAdjMonad (SysAdjMonad (M.AdjointT m)) = m

runSysAdjComonad :: SysAdjComonad s x -> SysAdjF s (SysComonad s (SysAdjG s x))
runSysAdjComonad (SysAdjComonad (W.AdjointT w)) = w

pattern UnSysAdjMonad a = SysAdjMonad (M.AdjointT a)
pattern UnSysAdjComonad a = SysAdjComonad (W.AdjointT a)

-- Kleisli and Cokleisli
data KleisliSAM s x y = KleisliSAM {unKleisliSAM' :: Kleisli (SysAdjMonad s) x y}deriving (C.Category,Arrow)
data CokleisliSAW s x y = CokleisliSAW {unCokleisliSAW' :: Cokleisli (SysAdjComonad s) x y}deriving (C.Category,Arrow)

unKleisliSAM :: KleisliSAM s x y -> x -> SysAdjMonad s y
unKleisliSAM = runKleisli . unKleisliSAM'

unCokleisliSAW :: CokleisliSAW s x y -> SysAdjComonad s x -> y
unCokleisliSAW = runCokleisli . unCokleisliSAW'

-- pattern UnSysAdjMonad a = SysAdjMonad (M.AdjointT a)

-- Profunctors

data ProCoAndKleisliSysAdj s x y = PCAKleisliSysAdj {unProCoAndKleisliSysAdj' :: Procompose (KleisliSAM s) (CokleisliSAW s) x y}
type PCAKSysAdj = ProCoAndKleisliSysAdj

data SysProMonad s (p :: * -> * -> *) a b = SysProMonad {unSysProMonad :: p a (SysAdjMonad s b)}
data SysProComonad s (p :: * -> * -> *) a b = SysProComonad {unSysProComonad :: p (SysAdjComonad s a) b} 
data SysProCoAndMonad s (p :: * -> * -> *) a b = SysProCoAndMonad {unSysProCoAndMonad :: p (SysAdjComonad s a) (SysAdjMonad s b)}

type family SysProfunctor s :: * -> * -> *

data SysPMonad s a b = SysPMonad {unSysPMonad :: SysProfunctor s a (SysAdjMonad s b) }
data SysPComonad s a b = SysPComonad {unSysPComonad :: SysProfunctor s (SysAdjComonad s a) b}
data SysPCoAndMonad s a b = SysPCoAndMonad {unSysPCoAndMonad :: SysProfunctor s (SysAdjComonad s a) (SysAdjMonad s b) }

-- covariant functors

data SysContrFunM s f a = SysContrFunM {unSysContrFunM :: (SysAdjMonad s :.: f) a} 
data SysContrFunW s f a = SysContrFunW {unSysContrFunW :: (SysAdjComonad s :.: f) a}

-- bifunctors

data SysBifunctorM s bif f g a = SysBifunctorM {unSysBifunctorM :: bif f g (SysAdjMonad s a)}
data SysBifunctorW s bif f g a = SysBifunctorW {unSysBifunctorW :: bif f g (SysAdjComonad s a)}

-- kan-extensions

data SysLan s h a = SysLan {unSysLan :: Lan (SysAdjG s) h a}
data SysRan s h a = SysRan {unSysRan :: Ran (SysAdjG s) h a}

data SysDensity s a = SysDensity {unSysDensity :: Density (SysAdjF s) a}
data SysCodensity s a = SysCodensity {unSysCoensity :: Codensity (SysAdjG s) a}

-- Types system primal wrapers

sysAdjMapMF :: CxtSystemCore s => Proxy s -> (SysAdjF s () -> SysAdjF s b) -> SysAdjMonad s b
sysAdjMapMF (p :: Proxy s) f = SysAdjMonad $ M.AdjointT $ (fmap . fmap) f $ M.runAdjointT $ unSysAdjMonad $ (return () :: SysAdjMonad s ())

sysAdjMapWG :: CxtSystemCore s => (SysAdjG s a -> SysAdjG s b) -> SysAdjComonad s a -> SysAdjComonad s b
sysAdjMapWG f = SysAdjComonad . W.AdjointT . fmap (fmap f) . W.runAdjointT . unSysAdjComonad

proCAKSysAdjToKleisli :: ProCoAndKleisliSysAdj s a b -> KleisliSAM s (SysAdjComonad s a) b  
proCAKSysAdjToKleisli (PCAKleisliSysAdj (Procompose k ck)) = (arr (unCokleisliSAW ck)) >>>  k 

proCAKSysAdjToCokleisli :: ProCoAndKleisliSysAdj s a b -> CokleisliSAW s a (SysAdjMonad s b)
proCAKSysAdjToCokleisli  (PCAKleisliSysAdj (Procompose k ck)) = ck >>> (arr (unKleisliSAM k)) 

unArrowPCAKSysAdj :: ProCoAndKleisliSysAdj s a b -> SysAdjComonad s a -> SysAdjMonad s b
unArrowPCAKSysAdj  (PCAKleisliSysAdj (Procompose k ck)) = (unKleisliSAM k) . (unCokleisliSAW ck) 

arrowToPCAKSysAdj :: KleisliSAM s c b -> CokleisliSAW s a c  -> ProCoAndKleisliSysAdj s a b
arrowToPCAKSysAdj x = PCAKleisliSysAdj . Procompose x

arrowToPCAKSAarr :: (c -> SysAdjMonad s b) -> (SysAdjComonad s a -> c) -> ProCoAndKleisliSysAdj s a b
arrowToPCAKSAarr f g = arrowToPCAKSysAdj (KleisliSAM $ Kleisli f) (CokleisliSAW $ Cokleisli g)

-- Objects and Subjects

type Object s = Inv.Free (SysAdjMonad s)
type Subject s = Inv.Free (SysAdjComonad s)

-- Arrows for Object and Subject

type ArrObject s r = Inv.Free (KleisliSAM s r)
type ArrSubject s r = Inv.Free (CokleisliSAW s r)

type ProObjSubject s r = Inv.Free (ProCoAndKleisliSysAdj s r)

-- Arrows for Object and Subject primal wrapers

objectToArrObject :: CxtSystemCore s => (forall x. r -> SysAdjMonad s x -> SysAdjMonad s x) -> Object s a -> ArrObject s r a
objectToArrObject f = mapFree (\ x -> KleisliSAM $ Kleisli (\y-> f y x) )

subjectToArrSubject :: (CxtSystemCore s) => (forall x. r -> SysAdjComonad s x -> SysAdjComonad s x) -> Subject s a -> ArrSubject s r a
subjectToArrSubject f = mapFree (\ x -> CokleisliSAW $ Cokleisli (\ y -> extract $ f (extract y) x) )

proObjSubjectSafe :: (CxtSystemCore s{-, Alternative (SysMonad s)-}) => ArrObject s r a -> ArrSubject s r a -> Maybe (ProObjSubject s r a)
proObjSubjectSafe (Transform (i1 :: (b <-> a)) f1) (Transform i2 f2) = Nothing
proObjSubjectSafe a1 a2 = return $ proObjSubject a1 a2

proObjSubject :: (CxtSystemCore s{-, Alternative (SysMonad s)-}) => ArrObject s r a -> ArrSubject s r a -> ProObjSubject s r a
proObjSubject Inv.Void _ = Inv.Void
proObjSubject Inv.Empty _ = Inv.Empty 
proObjSubject (Inv.Join f1 f2) (Inv.Join g1 g2) 
	= Inv.Join (proObjSubject  f1 g1) (proObjSubject f2 g2)
proObjSubject (Choose f1 f2) _ = Choose (mapFree (\x-> arrowToPCAKSysAdj x (arr id) ) f1) undefined 
proObjSubject _  (Choose g1 g2) = Choose undefined (mapFree (\x-> arrowToPCAKSysAdj (arr id) x ) g2) 
--proObjSubject (Transform (i1 :: (b <-> a)) f1) (Transform i2 f2) = Transform i1 (proObjSubject f1 f2) 

jointWith :: (forall x. f x)
	-> (forall x. g x)
	-> (forall x. f x -> g x -> t x)  
	-> Inv.Free f a -> Inv.Free g a -> Inv.Free t a
jointWith _ _ _ Inv.Void _ = Inv.Void
jointWith _ _ _ Inv.Empty _ = Inv.Empty
jointWith _ _ f (Inv.Free f1) (Inv.Free f2) = Inv.Free (f f1 f2)
jointWith ef eg f (Inv.Join f1 f2) (Inv.Join g1 g2)
	= Inv.Join (jointWith ef eg f f1 g1) (jointWith ef eg f f2 g2)
jointWith ef eg f (Choose f1 f2) _ = Choose (mapFree (\x-> f x eg) f1) undefined 
jointWith ef eg f _  (Choose g1 g2) = Choose undefined (mapFree (\x-> f ef x ) g2) 

jointWithPoint :: (forall x. g x -> f x)
	-> (forall x. f x -> g x)
	-> (forall x. f x -> g x -> t x)  
	-> Inv.Free f a -> Inv.Free g a -> Inv.Free t a
jointWithPoint _ _ _ Inv.Void _ = Inv.Void
jointWithPoint _ _ _ Inv.Empty _ = Inv.Empty
jointWithPoint _ _ f (Inv.Free f1) (Inv.Free f2) = Inv.Free (f f1 f2)
jointWithPoint ef eg f (Inv.Join f1 f2) (Inv.Join g1 g2)
	= Inv.Join (jointWithPoint ef eg f f1 g1) (jointWithPoint ef eg f f2 g2)
jointWithPoint ef eg f (Choose f1 f2) _ = Choose (mapFree (\x-> f x (eg x) ) f1) undefined 
jointWithPoint ef eg f _  (Choose g1 g2) = Choose undefined (mapFree (\x-> f (ef x) x ) g2) 

-- Instacess

instance CxtSystemCore s => Functor (SysAdjMonad s) where
  fmap f = SysAdjMonad . fmap f . unSysAdjMonad

instance CxtSystemCore s => Functor (SysAdjComonad s) where
  fmap f = SysAdjComonad . fmap f . unSysAdjComonad

instance  CxtSystemCore s => Applicative (SysAdjMonad s) where
  pure = SysAdjMonad . pure
  liftA2 f x = SysAdjMonad . liftA2 f (unSysAdjMonad x) . unSysAdjMonad

instance  CxtSystemCore s => Monad (SysAdjMonad s) where
  (>>=) m f = (SysAdjMonad . (>>= (unSysAdjMonad . f) )  . unSysAdjMonad) m

instance  CxtSystemCore s => Comonad (SysAdjComonad s) where
  extract = extract . unSysAdjComonad
  duplicate = SysAdjComonad . fmap SysAdjComonad . duplicate . unSysAdjComonad 

-- Utils

liftSysM :: (CxtSystemCore s, Traversable (SysAdjF s)) => SysMonad s a -> SysAdjMonad s a
liftSysM s = SysAdjMonad $ lift s

lowerSysW :: CxtSystemCore s => SysAdjComonad s a-> SysComonad s a
lowerSysW = lower . unSysAdjComonad

mapSysM :: (CxtSystemCore s, Traversable (SysMonad s), Applicative (SysAdjF s), Traversable (SysAdjF s)) 
	=> (SysMonad s a -> SysMonad s b) -> SysAdjMonad s a -> SysAdjMonad s b
mapSysM f (SysAdjMonad (M.AdjointT m )) = SysAdjMonad $ M.AdjointT $ fmap (sequenceA . fmap f . sequenceA) m

mapSysW :: CxtSystemCore s 
	=> (SysComonad s a -> SysComonad s b) -> SysAdjComonad s a -> SysAdjComonad s b
mapSysW f (SysAdjComonad s@(W.AdjointT ss)) = SysAdjComonad $ W.AdjointT $ 
	(\x-> fmap (\c-> fmap (\b-> fmap (const b) (extract c) ) x) ss ) $ f $ lower s  -- SysAdjComonad $ W.AdjointT $ fmap ( . fmap f . distribute) s

