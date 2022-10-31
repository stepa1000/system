{-# Language TypeOperators, TypeFamilies, FlexibleContexts
  , UndecidableInstances, ConstraintKinds, ScopedTypeVariables
  , RankNTypes, AllowAmbiguousTypes, TypeApplications, GADTs
  , MultiParamTypeClasses, DeriveGeneric, DataKinds
  , DerivingVia, BangPatterns
#-}
module Control.Core.Powsition where

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

data (:^^:) a b = Powsition a b

type instance SysAdjF (s1 :^^: s2) = SysAdjF s2
type instance SysAdjG (s1 :^^: s2) = SysAdjG s2
type instance SysMonad (s1 :^^: s2) = SysAdjMonad s1 :*: SysMonad s2
type instance SysComonad (s1 :^^: s2) = Sum (SysAdjComonad s1) (SysComonad s2)

-- syncyng :: AdjointT

-- for Monad Comonad

($^^) :: ( CxtSystemCore s1, CxtSystemCore s2
	, (SysAdjMonad s1 :*: SysMonad s2) ~ SysMonad (s1 :^^: s2)
	) 
	=> Proxy (s1,s2) -> SysAdjMonad s1 (SysAdjF s2 a) -> SysAdjMonad s2 a -> SysAdjMonad (s1 :^^: s2) a
($^^) (p :: Proxy (s1,s2)) s1 sm = SysAdjMonad $ M.AdjointT $
	fmap (\m-> (s1  :*:  m) ) $
	M.runAdjointT $ unSysAdjMonad $ sm

(@^^) :: ( CxtSystemCore s1, CxtSystemCore s2)
	=> SysAdjComonad s1 a -> SysAdjComonad s2 a -> [SysAdjComonad (s1 :^^: s2) a]
(@^^) s1 (SysAdjComonad (W.AdjointT sw)) = 
	[SysAdjComonad $ W.AdjointT $ fmap (InL . (\x-> fmap (\y-> (const y) <$> (extract x) ) s1) ) $ sw] ++ 
	[SysAdjComonad $ W.AdjointT $ fmap InR  sw]

-- for Kleisli, Cokleisli

($$^^) :: ( CxtSystemCore s1, CxtSystemCore s2
	, (SysAdjMonad s1 :*: SysMonad s2) ~ SysMonad (s1 :^^: s2)
	) 
	=> Proxy (s1,s2) -> KleisliSAM s1 a (SysAdjF s2 b) -> KleisliSAM s2 a b -> KleisliSAM (s1 :^^: s2) a b
($$^^) (p :: Proxy (s1,s2)) (KleisliSAM (Kleisli s1)) (KleisliSAM (Kleisli sm)) = 
	KleisliSAM $ Kleisli $ (\a-> (($^^) p) (s1 a) (sm a) )

(@@^^) :: ( CxtSystemCore s1, CxtSystemCore s2) 
	=> CokleisliSAW s1 a b -> CokleisliSAW s2 a b -> CokleisliSAW (s1 :^^: s2) a b
(@@^^) (CokleisliSAW (Cokleisli s1)) (CokleisliSAW (Cokleisli s2)) = CokleisliSAW $ Cokleisli (\ w -> f w (lower (unSysAdjComonad w) ) )
	where
		f w (InL w2) = s1 w2
		f w (InR _) = s2 (SysAdjComonad $ W.AdjointT $ fmap (\(InR w2)-> w2) $ W.runAdjointT $ unSysAdjComonad w)

-- for Procompos Kleisli, Cokleisli

(@$^^) :: ( CxtSystemCore s1, CxtSystemCore s2
	, (SysAdjMonad s1 :*: SysMonad s2) ~ SysMonad (s1 :^^: s2), MonadPlus (SysMonad s2), MonadPlus (SysMonad s1)
	, Traversable (SysAdjF s1), Traversable (SysAdjF s2)
	) 
	=> Proxy (s1,s2) -> PCAKSysAdj s1 a (SysAdjF s2 b) -> PCAKSysAdj s2 a b -> PCAKSysAdj (s1 :^^: s2) a b
(@$^^) p p1 p2 = (\f-> PCAKleisliSysAdj $ Procompose (KleisliSAM $ Kleisli id) f ) $ CokleisliSAW $ Cokleisli $ (\(CokleisliSAW (Cokleisli s1))-> s1 >>> 
		arr (either 
			(\x-> (($^^) p) x (SysAdjMonad $ lift $ mzero )  ) 
			(\x-> (($^^) p) (SysAdjMonad $ lift $ mzero) x) ) ) $ 
	((>>> arr Left) $ CokleisliSAW $ Cokleisli (unArrowPCAKSysAdj p1 )) @@^^ ((>>> arr Right) $ CokleisliSAW $ Cokleisli (unArrowPCAKSysAdj p2))

-- for Object, Subject

type ObjectAndAdjF s1 s2 = Inv.Free (SysAdjMonad s1 :.: SysAdjF s2)

(%^^) :: ( CxtSystemCore s1, CxtSystemCore s2, MonadPlus (SysMonad s2), MonadPlus (SysMonad s1)
	, Traversable (SysAdjF s1), Traversable (SysAdjF s2)) 
	=> Proxy (s1,s2) -> ObjectAndAdjF s1 s2 a -> Object s2 a -> Object (s1 :^^: s2) a 
(%^^) p o1 o2 = jointWith (Comp1 $ SysAdjMonad $ lift mzero) (SysAdjMonad $ lift mzero) 
	(\ x y -> ($^^) p (unComp1  x) y ) o1 o2

(^%^^) :: ( CxtSystemCore s1, CxtSystemCore s2) 
	=> (forall x. SysAdjComonad (s1 :^^: s2) x -> SysAdjComonad (s1 :^^: s2) x -> SysAdjComonad (s1 :^^: s2) x) 
	-> (forall x. SysAdjComonad s2 x -> SysAdjComonad s1 x) 
	-> (forall x. SysAdjComonad s1 x -> SysAdjComonad s2 x) 
	-> Subject s1 a -> Subject s2 a -> Subject (s1 :^^: s2) a 
(^%^^) t f g o1 o2 = jointWithPoint f g (\ x y -> (\l->(t (head l) (last l)) ) $ x @^^  y) o1 o2

-- for Arrow Objct, Subject

type ArrObjectAndAdjF s1 s2 r = Inv.Free (KleisliSAM s1 r :.: SysAdjF s2)

(%%^^) :: ( CxtSystemCore s1, CxtSystemCore s2, MonadPlus (SysMonad s2), MonadPlus (SysMonad s1)
	, Traversable (SysAdjF s1), Traversable (SysAdjF s2))  
	=> Proxy (s1,s2) -> ArrObjectAndAdjF s1 s2 a b -> ArrObject s2 a b -> ArrObject (s1 :^^: s2) a b
(%%^^) p o1 o2 = jointWith (Comp1 $ KleisliSAM $ Kleisli $ const $ SysAdjMonad $ lift mzero) (KleisliSAM $ Kleisli $ const $ SysAdjMonad $ lift mzero) 
	(\ x y -> ($$^^) p (unComp1  x) y ) o1 o2

(^^%^^) :: ( CxtSystemCore s1, CxtSystemCore s2) 
	=> (forall x. SysAdjComonad s2 x -> SysAdjComonad s1 x) 
	-> (forall x. SysAdjComonad s1 x -> SysAdjComonad s2 x) 
	-> ArrSubject s1 a b -> ArrSubject s2 a b -> ArrSubject (s1 :^^: s2) a b
(^^%^^) f g o1 o2 = jointWithPoint ( CokleisliSAW . Cokleisli . (g >>>) . (\(CokleisliSAW (Cokleisli s1))-> s1)  ) 
	( CokleisliSAW . Cokleisli . (f >>>) . (\(CokleisliSAW (Cokleisli s1))-> s1)  ) 
	(\ x y -> x @@^^  y) o1 o2

-- for Procompos Kleisli, Cokleisly in Object and Subject
--
type ProObjSubjectAndAdjF s1 s2 r = Inv.Free (PCAKSysAdj s1 r :.: SysAdjF s2)

(^^%%) :: ( CxtSystemCore s1, CxtSystemCore s2, MonadPlus (SysMonad s2), MonadPlus (SysMonad s1)
	, Traversable (SysAdjF s1), Traversable (SysAdjF s2))   
	=> (forall x. SysAdjComonad s2 x -> SysAdjComonad s1 x) 
	-> (forall x. SysAdjComonad s1 x -> SysAdjComonad s2 x) 
	-> Proxy (s1,s2) -> ProObjSubjectAndAdjF s1 s2 a b -> ProObjSubject s2 a b -> ProObjSubject (s1 :^^: s2) a b
(^^%%) f g p o1 o2 = jointWithPoint 
	(\(PCAKleisliSysAdj (Procompose k w)) 
		-> Comp1 $ PCAKleisliSysAdj $ Procompose (KleisliSAM $ Kleisli $ \_-> SysAdjMonad $ lift $ mzero ) (CokleisliSAW $ Cokleisli $ (g >>>) $ (\(CokleisliSAW (Cokleisli s1))-> s1) w) ) 
	(\(Comp1 (PCAKleisliSysAdj (Procompose k w))) 
		-> PCAKleisliSysAdj $ Procompose (KleisliSAM $ Kleisli $ \_-> SysAdjMonad $ lift $ mzero ) (CokleisliSAW $ Cokleisli $ (f >>>) $ (\(CokleisliSAW (Cokleisli s1))-> s1) w) )
	(\ x y-> ((@$^^) p) (unComp1 x) y ) o1 o2 -- (mapFree unProCoAndKleisliSysAdj' o1 ) (mapFree unProCoAndKleisliSysAdj' o2)

-- Tree Adjunction

data TreeAdj (n :: Nat) (b :: Bool) s = TreeAdj (Proxy n) (Proxy b) s

type instance SysAdjF (TreeAdj (n :: Nat) 'True s) = (SysAdjF s) :.: (MF.Free (SysAdjF (TreeAdj (n - 1) (1 <=? (n-1)) s)))
type instance SysAdjF (TreeAdj n 'False s) = (SysAdjF s)

type instance SysAdjG (TreeAdj n 'True s) = (CF.Cofree (SysAdjG (TreeAdj (n - 1) (1 <=? (n-1)) s))) :.: (SysAdjG s)
type instance SysAdjG (TreeAdj n 'False s) = (SysAdjG s)

type instance SysMonad (TreeAdj n b s) = SysMonad s
type instance SysComonad (TreeAdj n b s) = SysComonad s

treeAdj :: ( CxtSystemCore s, SysAdjMonad s a ~ SysAdjMonad (TreeAdj 0 'False s) a
	, SysAdjG (TreeAdj 0 'False s) ~ (SysAdjG s) 
	, SysAdjF (TreeAdj 0 'False s) ~ (SysAdjF s)
	, SysMonad (TreeAdj 0 'False s) ~ SysMonad s
	, Typeable s, Typeable a
	) 
	=> SysAdjMonad s a -> SysAdjMonad (TreeAdj 0 'False s) a
treeAdj (s :: SysAdjMonad s a) = fromJust $ cast s

data TreeAdjGADF s a where
	NodeTAF ::((SysAdjF s) :.: (MF.Free (TreeAdjGADF s))) a -> TreeAdjGADF s a
	LeafTAF :: SysAdjF s a -> TreeAdjGADF s a

instance Functor (SysAdjF s) => Functor (TreeAdjGADF s) where
	fmap f (LeafTAF s) = LeafTAF $ fmap f s
	fmap f (NodeTAF s) = NodeTAF $ fmap f s

instance Foldable (SysAdjF s) => Foldable (TreeAdjGADF s) where
	foldMap f (LeafTAF s) = foldMap f s
	foldMap f (NodeTAF s) = foldMap f s

instance Traversable (SysAdjF s) => Traversable (TreeAdjGADF s) where
	sequenceA (LeafTAF s) = LeafTAF <$> sequenceA s
	sequenceA (NodeTAF s) = NodeTAF <$> sequenceA s

data TreeAdjGADG s a = NodeTAG 
			(((CF.Cofree (TreeAdjGADG s)) :.: (SysAdjG s)) a) 
			(SysAdjG s a)

instance Functor (SysAdjG s) => Functor (TreeAdjGADG s) where
	fmap f (NodeTAG s fs) = NodeTAG (fmap f s) (fmap f fs)

instance Foldable (SysAdjG s) => Foldable (TreeAdjGADG s) where
	foldMap f (NodeTAG s fs) = (foldMap f s) <> (foldMap f fs)

instance Traversable (SysAdjG s) => Traversable (TreeAdjGADG s) where
	sequenceA (NodeTAG s fs) = f2 <$> sequenceA (s :*: fs)
		where
			f (NodeTAG s fs) = (s :*: fs) 
			f2 (s :*: fs) = (NodeTAG s fs)

instance (Distributive (SysAdjG s)) => Distributive (TreeAdjGADG s) where
	distribute s = (\(s :*: fs) -> (NodeTAG s fs)) $ distribute $ fmap f s
		where
			f (NodeTAG s fs) = (s :*: fs) 
			f2 (s :*: fs) = (NodeTAG s fs)

instance (Representable (SysAdjG s)) => Representable (TreeAdjGADG s) where
	type Rep (TreeAdjGADG s) = Either (WrappedRep (CF.Cofree (TreeAdjGADG s)), WrappedRep (SysAdjG s) ) (WrappedRep (SysAdjG s)) 
	tabulate f = NodeTAG (tabulate (f . Left . bimap WrapRep WrapRep) ) (tabulate (f . Right . WrapRep))
	index (NodeTAG s fs) = either id id . bimap (index s . bimap unwrapRep unwrapRep) (index fs . unwrapRep) -- index (s :*: fs) $ _b rs

instance (CxtSystemCore s) => Adjunction (TreeAdjGADF s) (TreeAdjGADG s) where
	unit = fmap f . (\(s :*: fs) -> (NodeTAG s fs)) . unit
		where
			f (R1 a) = LeafTAF a
			f (L1 a) = NodeTAF a -- $ Comp1 $ fmap return a
	counit = counit . f . fmap (\(NodeTAG s fs) -> (s :*: fs))
		where
			f (LeafTAF a) = R1 a
			f (NodeTAF a) = L1 a

unionTreeAdjGAD_F :: ( CxtSystemCore s1, CxtSystemCore s2, CxtSystemCore s3
	, Typeable s1, Typeable a, Traversable (SysAdjF s1), Traversable (SysAdjF s3)
	, Typeable s3, Typeable d
	) 
	=> (forall x y. SysAdjF s1 x -> SysAdjF s2 y -> SysAdjF s3 (x,y))
	-> TreeAdjGADF s1 a -> TreeAdjGADF s2 d -> TreeAdjGADF s3 (a,d)
unionTreeAdjGAD_F f (LeafTAF s1) (LeafTAF s2) = LeafTAF $ f s1 s2
unionTreeAdjGAD_F f (NodeTAF (Comp1 s1)) (NodeTAF (Comp1 s2)) = NodeTAF $ Comp1 $ (fmap . fmap) (\(These x1 y1)->(x1,y1) ) $
	fmap (\(x,y)-> MF.iterM (\tx-> MF.iterM (\yt-> join $ fmap (MF.wrap . fmap return) $ sequence $ fmap g $ unionTreeAdjGAD_F f tx yt ) (fmap (That) y) ) (fmap (This) x) ) $ f s1 s2
	where
		-- g2 ()
		g (xt,yt) = xt >>= (\x2-> yt >>= (\y2-> case (x2,y2) of 
			(This x, That y) -> return (These x y) 
			(These x1 y1,These x2 y2) -> return (These x1 y2)
			(This x,These x2 y2) -> return (These x y2)
			(These x1 y1, That y) -> return (These x1 y)
			))

unionTreeAdjGAD_G :: ( CxtSystemCore s1, CxtSystemCore s2, CxtSystemCore s3
	, Typeable s1, Typeable a, Typeable (SysAdjG s1) ,Traversable (SysAdjF s1), Traversable (SysAdjF s3)
	, Typeable s3, Typeable d, Typeable (SysAdjG s2), Typeable s2
	) 
	=> (forall x y. SysAdjG s1 x -> SysAdjG s2 y -> SysAdjG s3 (x,y))
	-> TreeAdjGADG s1 a -> TreeAdjGADG s2 d -> TreeAdjGADG s3 (a,d)
unionTreeAdjGAD_G f (NodeTAG (Comp1 s1) fs1) (NodeTAG (Comp1 s2) fs2) = NodeTAG (Comp1 $ g s1 s2) (f fs1 fs2)
	where	
		g (a :< fw) (a2 :< fw2) = (f a a2) :<
			(fmap (\(x,y)-> g x y) $ unionTreeAdjGAD_G f fw fw2)
