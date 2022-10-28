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

data TreeAdjGADF n b s a where
	NodeTAF :: ( KnownNat (n - 1), Typeable (1 <=? (n-1)), KnownNat n
		) 
		=> ((SysAdjF s) :.: (MF.Free (TreeAdjGADF (n - 1) (1 <=? (n-1)) s))) a -> TreeAdjGADF n b s a
	LeafTAF :: SysAdjF s a -> TreeAdjGADF 0 'False s a

instance Functor (SysAdjF s) => Functor (TreeAdjGADF n b s) where
	fmap f (LeafTAF s) = LeafTAF $ fmap f s
	fmap f (NodeTAF s) = NodeTAF $ fmap f s

instance Foldable (SysAdjF s) => Foldable (TreeAdjGADF n b s) where
	foldMap f (LeafTAF s) = foldMap f s
	foldMap f (NodeTAF s) = foldMap f s

instance Traversable (SysAdjF s) => Traversable (TreeAdjGADF n b s) where
	sequenceA (LeafTAF s) = LeafTAF <$> sequenceA s
	sequenceA (NodeTAF s) = NodeTAF <$> sequenceA s

data TreeAdjGADG n b s a = (KnownNat (n - 1), Typeable (1 <=? (n-1)), KnownNat n) 
		=> NodeTAG 
			(((CF.Cofree (TreeAdjGADG (n - 1) (1 <=? (n-1)) s)) :.: (SysAdjG s)) a) 
			(SysAdjG s a)

--	LeafTAG :: SysAdjG s a -> TreeAdjGADG 0 'False s a Distributive not Sum

instance Functor (SysAdjG s) => Functor (TreeAdjGADG n b s) where
	fmap f (NodeTAG s fs) = NodeTAG (fmap f s) (fmap f fs)

instance Foldable (SysAdjG s) => Foldable (TreeAdjGADG n b s) where
	foldMap f (NodeTAG s fs) = (foldMap f s) <> (foldMap f fs)

instance Traversable (SysAdjG s) => Traversable (TreeAdjGADG n b s) where
	sequenceA (NodeTAG s fs) = f2 <$> sequenceA (s :*: fs)
		where
			f (NodeTAG s fs) = (s :*: fs) 
			f2 (s :*: fs) = (NodeTAG s fs)

instance (Distributive (SysAdjG s), Distributive (TreeAdjGADG (n - 1) (1 <=? (n-1)) s)
		, KnownNat (n - 1), Typeable (1 <=? (n-1)), KnownNat n
		) => Distributive (TreeAdjGADG n b s) where
	distribute s = (\(s :*: fs) -> (NodeTAG s fs)) $ distribute $ fmap f s
		where
			f (NodeTAG s fs) = (s :*: fs) 
			f2 (s :*: fs) = (NodeTAG s fs)

instance (Representable (SysAdjG s), Representable (TreeAdjGADG (n - 1) (1 <=? (n-1)) s)
		, KnownNat (n - 1), Typeable (1 <=? (n-1)), KnownNat n
		-- , Adj.Rep (TreeAdjGADG n b s) ~ Adj.Rep (((CF.Cofree (TreeAdjGADG (n - 1) (1 <=? (n-1)) s)) :.: (SysAdjG s)) :*: ((SysAdjG s)))
		) => Representable (TreeAdjGADG n b s) where
	type Rep (TreeAdjGADG n b s) = Either (WrappedRep (CF.Cofree (TreeAdjGADG (n - 1) (1 <=? (n-1)) s)), WrappedRep (SysAdjG s) ) (WrappedRep (SysAdjG s)) 
-- GRep (((CF.Cofree (TreeAdjGADG (n - 1) (1 <=? (n-1)) s)) :.: (SysAdjG s)) :*: (SysAdjG s))
--		(((CF.Cofree (TreeAdjGADG (n - 1) (1 <=? (n-1)) s)) :.: (SysAdjG s)) :*: ((SysAdjG s)))
	tabulate f = NodeTAG (tabulate (f . Left . bimap WrapRep WrapRep) ) (tabulate (f . Right . WrapRep))
	index (NodeTAG s fs) = either id id . bimap (index s . bimap unwrapRep unwrapRep) (index fs . unwrapRep) -- index (s :*: fs) $ _b rs

--data SizeN n1 n2 f a = ((n1 <= n2) ~ True) => SizeN (f n1 a)

data SizeTreeF n ns b s a = (KnownNat n, KnownNat ns, (n <=? ns) ~ 'True) => SizeTreeF {unSizeTreeF :: !(TreeAdjGADF n b s a)} 
--	deriving (Functor)
--		via (TreeAdjGADF n b s)
data SizeTreeG n ns b s a = (KnownNat n, KnownNat ns, (n <=? ns) ~ 'True) => SizeTreeG {unSizeTreeG :: !(TreeAdjGADG n b s a)} deriving ()
-- type instance SizeNTree n family

type CxtSizeTree n ns s = (KnownNat n, KnownNat ns, (n <=? ns) ~ 'True
	, CxtSystemCore s, KnownNat ns, (ns <=? 4) ~ 'True )

instance (CxtSizeTree n ns s, Functor (SysAdjF s)) => Functor (SizeTreeF n ns b s) where
	fmap f (SizeTreeF a) = SizeTreeF $ fmap f a

instance (CxtSizeTree n ns s,Functor (SysAdjG s)) => Functor (SizeTreeG n ns b s) where
	fmap f (SizeTreeG a) = SizeTreeG $ fmap f a

instance (CxtSizeTree n ns s,Distributive (SysAdjG s)) 
		=> Distributive (SizeTreeG n ns b s) where 
	distribute !a = SizeTreeG !$ distribute !$ fmap unSizeTreeG a

instance (CxtSizeTree n ns s) 
		=> Adjunction (SizeTreeF n ns b s) (SizeTreeG n ns b s) where
	unit = _a . unit


unionTreeAdjGAD_F :: ( CxtSystemCore s1, CxtSystemCore s2, CxtSystemCore s3
	, Typeable s1, Typeable a, Traversable (SysAdjF s1), Traversable (SysAdjF s3)
	, Typeable s3, Typeable d
	) 
	=> (forall x y. SysAdjF s1 x -> SysAdjF s2 y -> SysAdjF s3 (x,y))
	-> TreeAdjGADF n b s1 a -> TreeAdjGADF n b s2 d -> TreeAdjGADF n b s3 (a,d)
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
	-> TreeAdjGADG n b s1 a -> TreeAdjGADG n b s2 d -> TreeAdjGADG n b s3 (a,d)
--unionTreeAdjGAD_G f (LeafTAG s) (LeafTAG s2) = LeafTAG $ f s s2
unionTreeAdjGAD_G f (NodeTAG (Comp1 s1) fs1) (NodeTAG (Comp1 s2) fs2) = NodeTAG (Comp1 $ g s1 s2) (f fs1 fs2)
	where	
		g (a :< fw) (a2 :< fw2) = (f a a2) :<
			(fmap (\(x,y)-> g x y) $ unionTreeAdjGAD_G f fw fw2)



{-


compileTreeAdjGADF :: CxtSystemCore s1  
	=> Proxy s1 -> TreeAdjGADF n b s1 a -> SysAdjF (TreeAdj n b s1) a
compileTreeAdjGADF _ (LeafTAF s1) = s1
compileTreeAdjGADF (p :: Proxy s1) ( NodeTAF (Comp1 s1)) 
	= coerce $ Comp1 $ fmap (hoistFree (compileTreeAdjGADF p) ) s1
	fmap (\(x,y)-> MF.foldFree (\fy-> -- fromJust $ cast
		MF.foldFree (\fx-> lift $ unionTreeAdjGADF f fx fy) x) y) $ _a $ f s1 s2



-}

unionTreeAdj :: ( CxtSystemCore s, SysMonad (TreeAdj n b s1) ~ SysMonad (TreeAdj n b s2)
	, Typeable s, Typeable a, Semigroup a
	) 
	=> Proxy (s1,s2,s3,a,Proxy n, Proxy b)
	-> (SysAdjG s1 a -> SysAdjG s2 a -> SysAdjG s3 a) 
	-> (SysAdjF s1 a -> SysAdjF s2 a -> SysAdjF s3 a)
	-> SysAdjMonad (TreeAdj n b s1) a -> SysAdjMonad (TreeAdj n b s2) a -> SysAdjMonad (TreeAdj n b s3) a
unionTreeAdj (p :: Proxy (s1,s2,s3,a,Proxy n,Proxy b)) g f (SysAdjMonad (M.AdjointT s1)) (SysAdjMonad (M.AdjointT s2)) = undefined {-fromJust $ do
	eqT @'True @b
	let (a1 :< sw1) = s1
	let (a2 :< sw2) = s2a
	undefined sw1 sw2
-}

{-
-- Not tree

type TreeAdjF fl fr = MF.Free (fl :+: fr)
type TreeAdjG gl gr = CF.Cofree (gl :*: gr)
data TreeAdj s = TreeAdj s

type instance SysAdjF (TreeAdj s) = TreeAdjF (SysAdjF s) (SysAdjF s)
type instance SysAdjG (TreeAdj s) = TreeAdjG (SysAdjG s) (SysAdjG s)
type instance SysMonad (TreeAdj s) = SysMonad s
type instance SysComonad (TreeAdj s) = SysComonad s


type TWrapSysMonad s a = SysAdjG s (SysMonad s ((SysAdjF s) a))
type TWrapSysComonad s a = SysAdjF s (SysComonad s ((SysAdjG s) a))

type TWrapSysMonadSum s a = SysAdjG s (SysMonad s (Either (SysAdjF s a) (MF.Free (SysAdjF s :+: SysAdjF s) a) ))
type TWrapCoSysMonadTreeSum s a = Cofree (SysAdjG s :*: SysAdjG s) (SysMonad s (Either (SysAdjF s a) (MF.Free (SysAdjF s :+: SysAdjF s) a) ))

type TWrapCoSysMonadTree s a = Cofree (SysAdjG s :*: SysAdjG s) (SysMonad s (MF.Free (SysAdjF s :+: SysAdjF s) a))
type TWrapFrSysComonadTree s a = MF.Free (SysAdjF s :+: SysAdjF s) (SysComonad s (Cofree (SysAdjG s :*: SysAdjG s) a))

treeAdjAdd :: ( CxtSystemCore s, Applicative (SysAdjG s)) 
	=> SysAdjMonad s a -> SysAdjMonad (TreeAdj s) a -> SysAdjMonad (TreeAdj s) a
treeAdjAdd (SysAdjMonad (M.AdjointT s1) :: SysAdjMonad s a) 
		(SysAdjMonad (M.AdjointT s2) :: SysAdjMonad (TreeAdj s) a) = SysAdjMonad $ M.AdjointT $ 
	f1 ((fmap . fmap) Left s1) ((fmap . fmap) Right s2) 
	where
		f1 :: TWrapSysMonadSum s a -> TWrapCoSysMonadTreeSum s a ->  TWrapCoSysMonadTree s a
		f1 s1 (a :< w) = _a s1 a w

combTreeAdjM :: ( CxtSystemCore s1, CxtSystemCore s2, CxtSystemCore s3, SysMonad s2 ~ SysMonad s1
		, SysMonad s3 ~ SysMonad s2 ) 
	=> Proxy (s1,s2,s3)
	-> (forall a. SysAdjF s1 a -> (SysAdjF s3 :+: SysAdjF s3) a) 
	-> (forall a. SysAdjF s2 a -> (SysAdjF s3 :+: SysAdjF s3) a)
	-> (forall a. SysAdjG s1 a -> SysAdjG s2 a -> SysAdjG s3 a)
	-> (forall a b. SysAdjG s3 a -> SysAdjG s3 b -> SysAdjG s3 (a,b))
	-> SysAdjMonad (TreeAdj s1) a -> SysAdjMonad (TreeAdj s2) a -> SysAdjMonad (TreeAdj s3) a
combTreeAdjM (p :: Proxy (s1,s2,s3)) g1 g2 f2 (fa1 :: (forall a b. SysAdjG s3 a -> SysAdjG s3 b -> SysAdjG s3 (a,b))) 
		(SysAdjMonad (M.AdjointT s1) :: SysAdjMonad (TreeAdj s1) a) 
		(SysAdjMonad (M.AdjointT s2) :: SysAdjMonad (TreeAdj s2) a) = SysAdjMonad $ M.AdjointT $ t1 s1 s2
	where 	
		t1 :: Cofree (SysAdjG s1 :*: SysAdjG s1) (SysMonad s1 (MF.Free (SysAdjF s1 :+: SysAdjF s1) a))
			-> Cofree (SysAdjG s2 :*: SysAdjG s2) (SysMonad s1 (MF.Free (SysAdjF s2 :+: SysAdjF s2) a))
			-> Cofree (SysAdjG s3 :*: SysAdjG s3) (SysMonad s1 (MF.Free (SysAdjF s3 :+: SysAdjF s3) a))
		t1 (a1 :< g1) (a2 :< g2) = (a1 >>= (\x-> (\y-> t2 x y) <$> a2)) :< 
			((\(x1 :*: y1) (x2 :*: y2)-> (\z-> z :*: z) $ fmap (\(Left x,Right y)-> t1 x y) $ fa1 (f2 x1 x2) (f2 y1 y2) ) (fmap Left g1) (fmap Right g2))
		t2 :: MF.Free (SysAdjF s1 :+: SysAdjF s1) a -> MF.Free (SysAdjF s2 :+: SysAdjF s2) a -> MF.Free (SysAdjF s3 :+: SysAdjF s3) a
		t2 r1 r2 = (hoistFree (g1 . t3) r1) >> (hoistFree (g2 . t3) r2)
		t3 (L1 a) = a
		t3 (R1 a) = a

combTreeAdjW :: ( CxtSystemCore s1, CxtSystemCore s2, CxtSystemCore s3, SysComonad s2 ~ SysComonad s1
		, SysComonad s3 ~ SysComonad s2, ComonadApply (SysComonad s1) ) 
	=> Proxy (s1,s2,s3)
	-> (forall a. SysAdjF s1 a -> (SysAdjF s3 :+: SysAdjF s3) a) 
	-> (forall a. SysAdjF s2 a -> (SysAdjF s3 :+: SysAdjF s3) a)
	-> (forall a. SysAdjG s1 a -> SysAdjG s2 a -> SysAdjG s3 a)
	-> (forall a b. SysAdjG s3 a -> SysAdjG s3 b -> SysAdjG s3 (a,b))
	-> SysAdjComonad (TreeAdj s1) a -> SysAdjComonad (TreeAdj s2) a -> SysAdjComonad (TreeAdj s3) a
combTreeAdjW (p :: Proxy (s1,s2,s3)) g1 g2 f2 (fa1 :: (forall a b. SysAdjG s3 a -> SysAdjG s3 b -> SysAdjG s3 (a,b))) 
		((SysAdjComonad (W.AdjointT s1)) :: SysAdjComonad (TreeAdj s1) a) 
		((SysAdjComonad (W.AdjointT s2)) :: SysAdjComonad (TreeAdj s2) a) = SysAdjComonad $ W.AdjointT $ t2 s1 s2
	where
		t1 :: Cofree (SysAdjG s1 :*: SysAdjG s1) a
			-> Cofree (SysAdjG s2 :*: SysAdjG s2) a
			-> Cofree (SysAdjG s3 :*: SysAdjG s3) a
		t1 (a1 :< g1) (a2 :< g2) = a1 :< 
			((\(x1 :*: y1) (x2 :*: y2)-> (\z-> z :*: z) $ fmap (\(Left x, Right y)-> t1 x y) $ fa1 (f2 x1 x2) (f2 y1 y2) ) (fmap Left g1) (fmap Right g2))
		t2 :: MF.Free (SysAdjF s1 :+: SysAdjF s1) (SysComonad s1 (Cofree (SysAdjG s1 :*: SysAdjG s1) a)) 
			-> MF.Free (SysAdjF s2 :+: SysAdjF s2) (SysComonad s1 (Cofree (SysAdjG s2 :*: SysAdjG s2) a)) 
			-> MF.Free (SysAdjF s3 :+: SysAdjF s3) (SysComonad s1 (Cofree (SysAdjG s3 :*: SysAdjG s3) a))
		t2 r1 r2 = (hoistFree (g1 . t3) r1) >>= (\x-> hoistFree (g2 . t3) (fmap (\y-> liftW2 t1 x y ) r2)  )
		t3 (L1 a) = a
		t3 (R1 a) = a

-- for Arrows: Kleisli and Cokleisli 

combTreeAdjArrM :: ( CxtSystemCore s1, CxtSystemCore s2, CxtSystemCore s3, SysMonad s2 ~ SysMonad s1
		, SysMonad s3 ~ SysMonad s2 ) 
	=> Proxy (s1,s2,s3)
	-> (forall a. SysAdjF s1 a -> (SysAdjF s3 :+: SysAdjF s3) a) 
	-> (forall a. SysAdjF s2 a -> (SysAdjF s3 :+: SysAdjF s3) a)
	-> (forall a. SysAdjG s1 a -> SysAdjG s2 a -> SysAdjG s3 a)
	-> (forall a b. SysAdjG s3 a -> SysAdjG s3 b -> SysAdjG s3 (a,b))
	-> KleisliSAM (TreeAdj s1) a b -> KleisliSAM (TreeAdj s2) a b -> KleisliSAM (TreeAdj s3) a b
combTreeAdjArrM (p :: Proxy (s1,s2,s3)) g1 g2 f2 (fa1 :: (forall a b. SysAdjG s3 a -> SysAdjG s3 b -> SysAdjG s3 (a,b))) 
		(KleisliSAM (Kleisli s1)) 
		(KleisliSAM (Kleisli s2)) = KleisliSAM $ Kleisli (\a->combTreeAdjM p g1 g2 f2 fa1 (s1 a) (s2 a) )

combTreeAdjArrW :: ( CxtSystemCore s1, CxtSystemCore s2, CxtSystemCore s3, SysComonad s2 ~ SysComonad s1
		, SysComonad s3 ~ SysComonad s2 ) 
	=> Proxy (s1,s2,s3)
	-> (forall a. SysAdjF s3 a -> (SysAdjF s1 :+: SysAdjF s1) a) 
	-> (forall a. SysAdjF s3 a -> (SysAdjF s2 :+: SysAdjF s2) a)
	-> (forall a. SysAdjG s3 a -> SysAdjG s1 a)
	-> (forall a. SysAdjG s3 a -> SysAdjG s2 a)
	-> CokleisliSAW (TreeAdj s1) a b -> CokleisliSAW (TreeAdj s2) a c -> CokleisliSAW (TreeAdj s3) a (b,c)
combTreeAdjArrW (p :: Proxy (s1,s2,s3)) g1 g2 f2 f1
		(CokleisliSAW (Cokleisli s1)) 
		(CokleisliSAW (Cokleisli s2)) = CokleisliSAW $ Cokleisli (\(SysAdjComonad (W.AdjointT x))
		-> ((s1 $ SysAdjComonad $ W.AdjointT $ t1 x),(s2 $ SysAdjComonad $ W.AdjointT $ t2 x)) )
	where	
		t1 :: MF.Free (SysAdjF s3 :+: SysAdjF s3) (SysComonad s1 (Cofree (SysAdjG s3 :*: SysAdjG s3) a))
		   -> MF.Free (SysAdjF s1 :+: SysAdjF s1) (SysComonad s1 (Cofree (SysAdjG s1 :*: SysAdjG s1) a))
		t1 = ((fmap . fmap) (hoistCofree ((\(x :*: y)-> (f2 x) :*: (f2 y) )))  . hoistFree (g1 . t3))
		t2 :: MF.Free (SysAdjF s3 :+: SysAdjF s3) (SysComonad s1 (Cofree (SysAdjG s3 :*: SysAdjG s3) a))
		   -> MF.Free (SysAdjF s2 :+: SysAdjF s2) (SysComonad s1 (Cofree (SysAdjG s2 :*: SysAdjG s2) a))
		t2 = ((fmap . fmap) (hoistCofree ((\(x :*: y)-> (f1 x) :*: (f1 y) )))  . hoistFree (g2 . t3))
		t3 (L1 a) = a
		t3 (R1 a) = a

-- for Procomposition

combTreeAdjProMW :: ( CxtSystemCore s1, CxtSystemCore s2, CxtSystemCore s3, SysMonad s2 ~ SysMonad s1
		, SysMonad s3 ~ SysMonad s2 , SysComonad s2 ~ SysComonad s1
		, SysComonad s3 ~ SysComonad s2) 
	=> Proxy (s1,s2,s3)
	-> (forall a. SysAdjF s1 a -> (SysAdjF s3 :+: SysAdjF s3) a) 
	-> (forall a. SysAdjF s2 a -> (SysAdjF s3 :+: SysAdjF s3) a)
	-> (forall a. SysAdjG s1 a -> SysAdjG s2 a -> SysAdjG s3 a)
	-> (forall a b. SysAdjG s3 a -> SysAdjG s3 b -> SysAdjG s3 (a,b))
	-> (forall a. SysAdjF s3 a -> (SysAdjF s1 :+: SysAdjF s1) a) 
	-> (forall a. SysAdjF s3 a -> (SysAdjF s2 :+: SysAdjF s2) a)
	-> (forall a. SysAdjG s3 a -> SysAdjG s1 a)
	-> (forall a. SysAdjG s3 a -> SysAdjG s2 a)
	-> PCAKSysAdj (TreeAdj s1) a b -> PCAKSysAdj (TreeAdj s2) a b -> PCAKSysAdj (TreeAdj s3) a b
combTreeAdjProMW p f1 f2 f3 f4 g1 g2 g3 g4 p1 p2 = (\f-> PCAKleisliSysAdj $ Procompose (KleisliSAM $ Kleisli id) f ) $ (arr (\(x,y)-> combTreeAdjM p f1 f2 f3 f4 x y ) <<<) $
	combTreeAdjArrW p g1 g2 g3 g4 (CokleisliSAW $ Cokleisli $ unArrowPCAKSysAdj p1) (CokleisliSAW $ Cokleisli $ unArrowPCAKSysAdj p2)
-}
{- t1 s1 s2
	where
		t1 :: SysAdjG (TreeAdj s1) (SysMonad (TreeAdj s1) (SysAdjF (TreeAdj s1) a)) -> SysAdjG (TreeAdj s2) (SysMonad (TreeAdj s2) (SysAdjF (TreeAdj s2) a)) 
			-> SysAdjG (TreeAdj s3) (SysMonad s2 ((SysAdjF (TreeAdj s1) a), (SysAdjF (TreeAdj s2) a)))
		t1 a b = (\(x1 :*: y1) (x2 :*: y2) -> fmap (\ x y -> (fa1 x y) :*: (fa1 y x))
			(f2 x1 x2) (f2 y1 y2) ) (unwrap a) (unwrap b)
-}

{-
data TreeAdjF f a =
	CompF (((TreeAdjF f :+: TreeAdjF f) :.: f) a)
	| AdjF ( f a)

data TreeAdjG g a =
	CompG ((g :.: (TreeAdjG g :*: TreeAdjG g)) a)
	| AdjG (g a )
	deriving Generic1

instance Functor f => Functor (TreeAdjF f) where
  fmap f (CompF (Comp1 (L1 fl ) )) = CompF $ Comp1 $ L1 $ (fmap . fmap) f fl
  fmap f (CompF (Comp1 (R1 fl ) )) = CompF $ Comp1 $ R1 $ (fmap . fmap) f fl
  fmap f (AdjF fa) = AdjF $ fmap f fa

instance Functor f => Functor (TreeAdjG f) where
  fmap f (CompG (Comp1 g)) = CompG $ Comp1 $ fmap (\(g1 :*: g2)-> (fmap f g1) :*: (fmap f g2) ) g
  fmap f (AdjG fa) = AdjG $ fmap f fa

instance Distributive f => Distributive (TreeAdjG f) where
  distribute fg = CompG $ Comp1 $ fmap distribute $ distribute $ fmap (\(CompG (Comp1 g))->g) fg  

instance (Representable f, Generic1 f) => Representable (TreeAdjG f)

instance Adjunction f g => Adjunction (TreeAdjF f) (TreeAdjG g) where
  unit a = AdjG $ fmap AdjF $ unit a
  counit (CompF (Comp1 taf)) = _a $ t2 $ fmap (counit . fmap t ) taf
	where
		t2 (L1 f) = cozipL f
		t2 (R1 f) = cozipL f
		t (CompG (Comp1 g)) = fmap Left g
		t (AdjG ga) = fmap Right ga
-}
