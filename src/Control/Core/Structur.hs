{-# Language TypeOperators, TypeFamilies, FlexibleContexts
  , UndecidableInstances, ConstraintKinds, ScopedTypeVariables
  , RankNTypes, AllowAmbiguousTypes, TypeApplications, GADTs
  , MultiParamTypeClasses, DeriveGeneric, DataKinds
  , DerivingVia, BangPatterns, InstanceSigs
  , FlexibleInstances
#-}
module Control.Core.Structur where

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
import Data.Functor.Coyoneda

import Data.Distributive
import Data.Either
import Data.Typeable
import Data.Maybe

import Data.Bifunctor
import Data.These
import Data.Functor.Identity
import Data.Dynamic

-- import Data.Dynamic as D

import Unsafe.Coerce
{-
data SetGetSysF s a b c d = SetGetSysF 
	{unSetGetSysF :: SysProfunctor s (SysAdjF s c) (SysAdjF s d) 
			-> SysProfunctor s a b
	} 

data SetGetSysG s a b c d = SetGetSysG 
	{unSetGetSysG :: SysProfunctor s (SysAdjG s c) (SysAdjG s d) 
			-> SysProfunctor s a b
	} 
-}

type family ElemAdjF (f :: * -> *) where
 ElemAdjF (EnvT e f) = EnvT e (ElemAdjF f)
 ElemAdjF (WriterT e f) = WriterT e (ElemAdjF f)
 ElemAdjF (f1 :.: f2) = (ElemAdjF f2 :.: f1)
 ElemAdjF (f1 :+: f2) = (f1 :+: ElemAdjF f2)
 ElemAdjF (MF.Free f) = MF.Free (ElemAdjF f) 
 ElemAdjF (Yoneda f) = Yoneda (ElemAdjF f)
 ElemAdjF (Coyoneda f) = Coyoneda (ElemAdjF f)
 ElemAdjF Identity = Identity

type family ElemAdjG (f :: * -> *) where -- :: * -> *
 ElemAdjG (ReaderT e g) = ReaderT e (ElemAdjG g)
 ElemAdjG (TracedT e g) = TracedT e (ElemAdjG g)
 ElemAdjG (g1 :.: g2) = g1 :.: (ElemAdjG g2)
 ElemAdjG (g1 :*: g2) = (g1 :*: ElemAdjG g2)
 ElemAdjG (Cofree g) = Cofree (ElemAdjG g)
 ElemAdjG (Yoneda g) = Yoneda (ElemAdjG g)
 ElemAdjG (Coyoneda g) = Coyoneda (ElemAdjG g)
 ElemAdjG Identity = Identity
{-
data DataElemAdjF f a where
	EAEnvT :: Functor f => EnvT e (DataElemAdjF f ) a -> DataElemAdjF (EnvT e f) a
	EAWriterT :: Functor f => WriterT e (DataElemAdjF f) a -> DataElemAdjF (WriterT e f) a
--	EACompF :: (Functor f1, Functor f2) => (DataElemAdjF f2 :.: f1) a -> DataElemAdjF (f2 :.: f1) a
--	EASumProdF :: (Functor f1, Functor f2) => (f1 :+: DataElemAdjF f2) a -> DataElemAdjF (f1 :+: f2) a	
	EAFree :: Functor f => MF.Free (DataElemAdjF f) a -> DataElemAdjF (MF.Free f) a
	EAYonedaF :: Functor f => Yoneda (DataElemAdjF (ElemAdjF f)) a -> DataElemAdjF (Yoneda f) a
	EACoyonedaF :: Functor f => Coyoneda (DataElemAdjF f) a -> DataElemAdjF (Coyoneda f) a
	EAIdF :: Identity a -> DataElemAdjF Identity a	
-}
data DataElemAdjF a where
	EAEnvT :: EnvT Dynamic DataElemAdjF a -> DataElemAdjF a
	EAWriterT :: WriterT [Dynamic] DataElemAdjF a -> DataElemAdjF a
--	EACompF :: (Functor f1, Functor f2) => (DataElemAdjF f2 :.: f1) a -> DataElemAdjF (f2 :.: f1) a
--	EASumProdF :: (Functor f1, Functor f2) => (f1 :+: DataElemAdjF f2) a -> DataElemAdjF (f1 :+: f2) a	
	EAFree :: MF.Free DataElemAdjF a -> DataElemAdjF a
	EAYonedaF :: Yoneda DataElemAdjF a -> DataElemAdjF a
	EACoyonedaF :: Coyoneda DataElemAdjF a -> DataElemAdjF a
	EAIdF :: Identity a -> DataElemAdjF a	

instance Functor DataElemAdjF where
	fmap f ( (EAEnvT a)) =  EAEnvT $ fmap f a 
	fmap f ( (EAWriterT a)) =  EAWriterT $ fmap f a 
--	fmap f ( (EACompF a)) =  EACompF $ fmap f a 
--	fmap f ( (EASumProdF a)) =  EASumProdF $ fmap f a 
	fmap f ( (EAFree a)) =  EAFree $ fmap f a 
	fmap f ( (EAYonedaF a)) =  EAYonedaF $ fmap f a 
	fmap f ( (EACoyonedaF a)) =  EACoyonedaF $ fmap f a 
	fmap f ( (EAIdF a)) =  EAIdF $ fmap f a 

data DataElemAdjG a = DataElemAdjG { 
	eaReaderT :: ReaderT Dynamic DataElemAdjG a ,
	eaTracedT :: TracedT [Dynamic] DataElemAdjG a ,
--	eaCompG :: (g1 :.: ElementaryAdjG g2) a -> DataElemAdjG (g1 :.: g2) a
--	eaSumProdG :: (g1 :*: ElementaryAdjG g2) a -> DataElemAdjG (g1 :*: g2) a 
--	eaCompComb :: CompCombG g a
	eaCofree :: Cofree DataElemAdjG a,
	eaYonedaG :: Yoneda DataElemAdjG a,
	eaCoyonedaG :: Coyoneda DataElemAdjG a,
	eaIdG :: Identity a
	}

instance Functor DataElemAdjG where
	fmap f a = DataElemAdjG 
		{ eaReaderT = f <$> eaReaderT a
		, eaTracedT = f <$> eaTracedT a
		, eaCofree = f <$> eaCofree a
		, eaYonedaG = f <$> eaYonedaG a
		, eaCoyonedaG = f <$> eaCoyonedaG a
		, eaIdG = f <$> eaIdG a		
		}

instance Distributive DataElemAdjG where
	distribute = f2 . distribute . fmap f
		where
			f a = eaReaderT a :*: (eaTracedT a :*: (eaCofree a :*: (eaYonedaG a :*: (eaCoyonedaG a :*: (eaIdG a))))) 
			f2 (eaReaderTa :*: (eaTracedTa :*: (eaCofreea :*: (eaYonedaGa :*: (eaCoyonedaGa :*: (eaIdGa)))))) 
				= DataElemAdjG 
					{ eaReaderT = eaReaderTa
					, eaTracedT = eaTracedTa
					, eaCofree = eaCofreea
					, eaYonedaG = eaYonedaGa
					, eaCoyonedaG = eaCoyonedaGa
					, eaIdG = eaIdGa
					}

class StructurSysAdj s a where
	getSysAdjF :: Proxy s -> a -> SysAdjF s ()
	setSysAdjF :: SysAdjF s () -> a -> a

instance (StructurSysAdj s1 a1, StructurSysAdj s2 a2
	, SysAdjF (s1 :##: s2) ~ (SysAdjF s2 :.: SysAdjF s1)
	, CxtSystemCore s1, CxtSystemCore s2
	) => StructurSysAdj (s1 :##: s2) (a1,a2) where
	getSysAdjF (p :: Proxy (s1 :##: s2)) (a1,a2) = Comp1 $ fmap (const (getSysAdjF (Proxy :: Proxy s1) a1)) $ (getSysAdjF (Proxy :: Proxy s2) a2)
	setSysAdjF (Comp1 s :: SysAdjF (s1 :##: s2) ()) (a1,a2) = ((\x-> setSysAdjF @s1 x a1) $ extractL s, (\x-> setSysAdjF @s2 x a2) $ fmap (const ()) s) 

instance (StructurSysAdj s1 a1, StructurSysAdj s2 a2
	, SysAdjF (s1 :+*: s2) ~ (SysAdjF s1 :+: SysAdjF s2)
	, CxtSystemCore s1, CxtSystemCore s2
	) => StructurSysAdj (s1 :+*: s2) (These a1 a2) where
	getSysAdjF (p :: Proxy (s1 :+*: s2)) (These a1 a2) = R1 $ (getSysAdjF (Proxy :: Proxy s2) a2)
	getSysAdjF (p :: Proxy (s1 :+*: s2)) (That a2) = R1 $ (getSysAdjF (Proxy :: Proxy s2) a2)
	getSysAdjF (p :: Proxy (s1 :+*: s2)) (This a1) = L1 $ (getSysAdjF (Proxy :: Proxy s1) a1)
	setSysAdjF (R1 s :: SysAdjF (s1 :+*: s2) ()) (These a1 a2) = These a1 (setSysAdjF @s2 s a2) 
	setSysAdjF (R1 s :: SysAdjF (s1 :+*: s2) ()) (That a2) = That (setSysAdjF @s2 s a2) 
	setSysAdjF (L1 s :: SysAdjF (s1 :+*: s2) ()) (These a1 a2) = These (setSysAdjF @s1 s a1) a2 
	setSysAdjF (L1 s :: SysAdjF (s1 :+*: s2) ()) (This a1) = This (setSysAdjF @s1 s a1)
	setSysAdjF _ _ = error "setSysAdjF"

type ProSysAdjMonad p s a b = p (SysAdjF s a) (SysMonad s (SysAdjF s b))
data RunSysPMonad s a b = RunSysPMonad {unRunSysPMonad :: SysProfunctor s (SysAdjF s a) (SysMonad s (SysAdjF s b)) }

runSysPMonad :: (Profunctor (SysProfunctor s), Arrow (SysProfunctor s), ArrowApply (SysProfunctor s) --, Closed (SysProfunctor s)
	, CxtSystemCore s, Strong (SysProfunctor s)
	) => SysPMonad s a b -> RunSysPMonad s a b
runSysPMonad (SysPMonad p) = RunSysPMonad $ (>>> app) $ rmap (Arr.first arr) $ lmap (\a->(extractL a,a)) $ first' $ rmap (\(UnSysAdjMonad s) -> rightAdjunct $ const s) p

execSysPMonad :: (Profunctor (SysProfunctor s), Arrow (SysProfunctor s), ArrowApply (SysProfunctor s) --, Closed (SysProfunctor s)
	, CxtSystemCore s, Strong (SysProfunctor s)
	) => SysPMonad s a b -> SysProfunctor s (SysAdjF s a) (SysMonad s (SysAdjF s b))
execSysPMonad = unRunSysPMonad . runSysPMonad

type FreeSysAMonad s = MF.IterT (SysAdjMonad s)

--flipAdj :: (Adjunction f g, Monad m) => m (f a) -> g (m (f a))closed
--flipAdj mf = _a $ fmap (\f->(f, tabulateAdjunction )) mf

cycleFM :: (CxtSystemCore s, Applicative (SysAdjF s)) => SysAdjMonad s x -> (SysAdjF s x -> Maybe (SysAdjF s y)) -> FreeSysAMonad s y
cycleFM (UnSysAdjMonad s) a = untilJust $ UnSysAdjMonad $ (fmap . fmap) sequenceA $ (fmap . fmap) a $ s  -- undefined -- MF.unfold 

runCycleFM :: (CxtSystemCore s, Traversable (SysAdjF s), StructurSysAdj s a) => a -> FreeSysAMonad s y -> SysMonad s (SysAdjF s y)
runCycleFM a (s :: FreeSysAMonad s y) = MF.foldM (\(UnSysAdjMonad sam)-> fmap (extractL) $ join $ fmap sequence $ indexAdjunction sam (getSysAdjF (Proxy @s) a)) (s >>= f)
	where
		f y = lift $ sysAdjMapMF Proxy ((fmap . fmap) (const y) . duplicateL)

type FreeSysComonad s = CFi.CoiterT (SysAdjComonad s)

flipWM :: (Comonad w,Monad m) => w (m a) -> m (w a)
flipWM wm = do
	a <- extract wm
	return $ extend (const a) wm

cycleCFM :: CxtSystemCore s => (SysAdjComonad s x -> SysAdjMonad s x) -> SysAdjComonad s (SysAdjMonad s x) -> FreeSysComonad s (SysAdjMonad s x)
cycleCFM f sacsam = CFi.unfold (\wm-> (>>= f) $ flipWM wm) sacsam

runToCycleCFM :: CxtSystemCore s => (FreeSysComonad s (SysAdjMonad s x) -> Bool) -> FreeSysComonad s (SysAdjMonad s x) -> FreeSysComonad s (SysAdjMonad s x)
runToCycleCFM f fc = g $ fmap (\x->(x,f x)) $ duplicate fc
	where
		g (CoiterT wac) = (\((x,y),t)-> case y of
			True -> x
			False -> g t
			) $ extract wac

{-	gsAdjSysF :: Proxy s -> Lens' a (SysAdjF s ())
	gsAdjSysG :: Proxy s -> Lens' a (SysAdjG s ())

instance (StructurSysAdj s1 a1, StructurSysAdj s2 a2
	, SysAdjF (s1 :##: s2) ~ (SysAdjF s2 :.: SysAdjF s1)
	) => StructurSysAdj (s1 :##: s2) (a1,a2) where
	gsAdjSysF :: Proxy (s1 :##: s2) -> Lens' a (SysAdjF (s1 :##: s2) ())
	gsAdjSysF (p :: Proxy (s1 :##: s2)) = lens (\(a1,a2)-> Comp1 $ (const (a1^.(gsAdjSysF (Proxy :: Proxy s1)))) <$> (a2^.(gsAdjSysF (Proxy :: Proxy s2))) )
		(\ (a1,a2) (Comp1 ff) -> (set (gsAdjSysF (Proxy :: Proxy s1)) a1 (extractL ff), set (gsAdjSysF (Proxy :: Proxy s2)) a2 (fmap (const ()) ff)) )
	gsAdjSysG (p :: Proxy (s1 :##: s2)) = lens (\(a1,a2)-> Comp1 $ (const (a2^.(gsAdjSysG (Proxy :: Proxy s2)))) <$> (a1^.(gsAdjSysG (Proxy :: Proxy s1))))
		(\ (a1,a2) (Comp1 ff) -> (set (gsAdjSysG (Proxy :: Proxy s1)) a1 (fmap (const ()) ff)
			, set (gsAdjSysG (Proxy :: Proxy s1)) a2 (indexAdjunction (ff) (a1^.(gsAdjSysF (Proxy :: Proxy s1) ))) ) )
-}
