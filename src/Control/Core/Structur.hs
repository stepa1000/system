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

type family ElemAdjF s :: * -> *
type family ElemAdjG s :: * -> *
{-
type family SysAdjF s :: * -> *
type family SysAdjG s :: * -> *
type family SysMonad s :: * -> *
type family SysComonad s :: * -> *
-}

type CxtElemAdj f = (Adjunction (ElemAdjF f) (ElemAdjG f)
	, Functor (ElemAdjG f))

data VarAdj e 
data EventAdj e
data FreeAdj f
data YonedaAdj f
data CoyonedaAdj f
data IdAdj

type instance ElemAdjF (VarAdj e) = Env e
type instance ElemAdjG (VarAdj e) = Reader e

type instance ElemAdjF (EventAdj e) = Writer e
type instance ElemAdjG (EventAdj e) = Traced e

type instance ElemAdjF (FreeAdj f) = MF.Free (ElemAdjF f)
type instance ElemAdjG (FreeAdj g) = Cofree (ElemAdjG g)

type instance ElemAdjF (f1 :##: f2) = (ElemAdjF f2 :.: ElemAdjF f1) 
type instance ElemAdjG (g1 :##: g2) = (ElemAdjG g1 :.: ElemAdjG g2) 

type instance ElemAdjF (f1 :+*: f2) = (ElemAdjF f1 :+: ElemAdjF f2) 
type instance ElemAdjG (g1 :+*: g2) = (ElemAdjG g1 :*: ElemAdjG g2)

type instance ElemAdjF (YonedaAdj f) = Yoneda (ElemAdjF f)
type instance ElemAdjG (YonedaAdj g) = Yoneda (ElemAdjG g)

type instance ElemAdjF (CoyonedaAdj f) = Coyoneda (ElemAdjF f)
type instance ElemAdjG (CoyonedaAdj g) = Coyoneda (ElemAdjG g)

type instance ElemAdjF IdAdj = Identity
type instance ElemAdjG IdAdj = Identity

type ElemAdjointM f = M.Adjoint (ElemAdjF f) (ElemAdjG f)
type ElemAdjointW f = W.Adjoint (ElemAdjF f) (ElemAdjG f)

mapEAdjF :: CxtElemAdj f => (ElemAdjF f () -> ElemAdjF f a) -> ElemAdjointM f a
mapEAdjF f = M.AdjointT $ (fmap . fmap) f $ M.runAdjointT $ return ()

mapEAdjFbind :: CxtElemAdj f => (ElemAdjF f a -> ElemAdjF f b) -> ElemAdjointM f a -> ElemAdjointM f b
mapEAdjFbind f a = M.AdjointT $ (fmap . fmap) f $ M.runAdjointT $ a

compEAdj :: (CxtElemAdj f, CxtElemAdj g) => ElemAdjointM f a -> ElemAdjointM g b -> ElemAdjointM (f :##: g) (a,b)
compEAdj (M.AdjointT e1) (M.AdjointT e2) = M.AdjointT $ fmap (Identity . Comp1) $ Comp1 $ fmap (\(Identity g2)->
	 fmap (\(Identity g1)-> fmap (\a->fmap (\b->(b,a)) g2) g1) e2) e1

combEAdj :: (CxtElemAdj f, CxtElemAdj g) 
	=> ElemAdjointW f a -> ElemAdjointW g b -> [ElemAdjointW (f :+*: g) (Either a b)]
combEAdj (W.AdjointT e1) (W.AdjointT e2) = fmap W.AdjointT $
	[L1 ((fmap . fmap) (\g1-> (fmap Left g1) :*: (fmap Right $ extract $ extractL $ e2))  e1)] ++ 
	[R1 ((fmap . fmap) (\g2-> (fmap Left $ extract $ extractL $ e1) :*: (fmap Right g2)) e2)]

getEnvAdjM :: CxtElemAdj (VarAdj e) => Proxy e -> ElemAdjointM (VarAdj e) e
getEnvAdjM (p :: Proxy e) = mapEAdjF @(VarAdj e) (extend (fst . runEnv))

getEnvAdjW :: ElemAdjointW (VarAdj e) x -> e
getEnvAdjW (W.AdjointT a) = (fst . runEnv) a

getEventAdjM :: (CxtElemAdj (EventAdj e), Monoid e) => Proxy e -> ElemAdjointM (EventAdj e) e
getEventAdjM (p :: Proxy e) = mapEAdjF @(EventAdj e) (return . snd . runWriter)

getEventAdjW :: ElemAdjointW (EventAdj e) x -> e
getEventAdjW (W.AdjointT a) = (snd . runWriter) a

getFreeAdjM :: CxtElemAdj (FreeAdj f) 
	=> Proxy f -> ElemAdjointM (FreeAdj f) (MF.Free (ElemAdjF f) ())
getFreeAdjM (p :: Proxy f) = mapEAdjF @(FreeAdj f) (\x-> fmap (const x) x)

getFreeAdjW :: (CxtElemAdj (FreeAdj f), CxtElemAdj f) 
	=> ElemAdjointW (FreeAdj f) x -> MF.Free (ElemAdjF f) (ElemAdjG f x)
getFreeAdjW (W.AdjointT a) = fmap (\(Identity b)->fmap extract $ unwrap b) a

runYonedaAdjM :: (CxtElemAdj (YonedaAdj f), CxtElemAdj f)
	=> Proxy f 
	-> (a -> b) -> ElemAdjointM (YonedaAdj f) a 
	-> ElemAdjointM (YonedaAdj f) (a, b)
runYonedaAdjM (p :: Proxy f) f (n :: ElemAdjointM (YonedaAdj f) a) = mapEAdjFbind @(YonedaAdj f)
	(\(Yoneda g)-> Yoneda (\t-> fmap (\a->t (a,f a)) (g id)) ) n

runYonedaAdjW :: (CxtElemAdj (YonedaAdj f), CxtElemAdj f)
	=> Proxy f 
	-> (ElemAdjG f a -> b) -> ElemAdjointW (YonedaAdj f) a 
	-> ElemAdjF f b
runYonedaAdjW (p :: Proxy f) f (n :: ElemAdjointW (YonedaAdj f) a) = 
	(\(Yoneda g)-> g f) $ 
	fmap lowerYoneda $ W.runAdjoint @(Yoneda (ElemAdjF f)) n

hositCoyonedaAdjM :: (CxtElemAdj (YonedaAdj f), CxtElemAdj f)
	=> (forall x. ElemAdjF f1 x -> ElemAdjF f2 x)	
	-> (forall x. ElemAdjG f1 x -> ElemAdjG f2 x)	
	-> ElemAdjointM (CoyonedaAdj f1) a 
	-> ElemAdjointM (CoyonedaAdj f2) a
hositCoyonedaAdjM f1 f2 (M.AdjointT a) = M.AdjointT $
	(fmap . fmap) (hoistCoyoneda f1) $ 
	hoistCoyoneda f2 a

type instance SysAdjF (VarAdj e) = Env e
type instance SysAdjG (VarAdj e) = Reader e

type instance SysAdjF (EventAdj e) = Writer e
type instance SysAdjG (EventAdj e) = Traced e

type instance SysAdjF (FreeAdj f) = MF.Free (ElemAdjF f)
type instance SysAdjG (FreeAdj g) = Cofree (ElemAdjG g)

type instance SysAdjF (YonedaAdj f) = Yoneda (ElemAdjF f)
type instance SysAdjG (YonedaAdj g) = Yoneda (ElemAdjG g)

type instance SysAdjF (CoyonedaAdj f) = Coyoneda (ElemAdjF f)
type instance SysAdjG (CoyonedaAdj g) = Coyoneda (ElemAdjG g)

type instance SysAdjF IdAdj = Identity
type instance SysAdjG IdAdj = Identity

liftEAdj :: ( SysAdjF s ~ ElemAdjF s
	, SysAdjG s ~ ElemAdjG s
	, CxtSystemCore s, CxtElemAdj s  
	, Typeable (SysAdjF s), Typeable (ElemAdjF s)
	, Typeable (SysAdjG s), Typeable (ElemAdjG s)
	, Typeable (SysMonad s), Typeable x, Typeable s
	) 
	=> Proxy s -> ElemAdjointM s x -> SysAdjMonad s x  
liftEAdj (p :: Proxy s) (M.AdjointT e :: ElemAdjointM s x) = fromJust $ cast $ M.AdjointT $ fmap (\(Identity a)->return @(SysMonad s) a) e

lowerEAdj :: ( SysAdjF s ~ ElemAdjF s
	, SysAdjG s ~ ElemAdjG s
	, CxtSystemCore s, CxtElemAdj s 
	, Typeable (SysAdjF s), Typeable (ElemAdjF s)
	, Typeable (SysAdjG s), Typeable (ElemAdjG s)
	, Typeable (SysComonad s), Typeable x, Typeable s
	) 
	=> Proxy s -> SysAdjComonad s x -> ElemAdjointW s x
lowerEAdj (p :: Proxy s) (UnSysAdjComonad a) = fromJust $ cast $ W.AdjointT $ fmap (Identity . extract) $ a

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
