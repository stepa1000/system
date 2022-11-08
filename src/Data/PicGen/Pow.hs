{-# Language TypeFamilies, DeriveAnyClass, TypeApplications
  , TypeOperators
#-}

module Data.PicGen.Pow where

import GHC.Generics
import Prelude as Pre
import Extra
import Linear

import Codec.Picture
import System.Random

import Control.Applicative
import Control.Monad.Logic
import Control.Monad.Reader
import Control.Monad.Writer as Wr

import Control.Comonad.Trans.Traced as Tr
import Control.Comonad.Trans.Env
import Control.Comonad
import Control.Comonad.Trans.Class

import Control.Comonad.Trans.Store

import Data.List.NonEmpty as NE
import Data.Word
import Data.Proxy 
import Data.PicGen.Core

import Data.Functor.Adjunction
import qualified Data.Vector as Vec
import Data.Function
import Data.Maybe

import Control.Core.System
import Control.Core.Composition
import Control.Core.Structur

import Control.Core.Postlude
import Control.Simple.Joing

bsbRR :: Int -> Int -> (Float,Float)
bsbRR n' k' = (x,y)
	where
		n = intToFloat n'
		k = intToFloat k'
		z = (2**(2*n) + 2**k)
		x = (2**(2*n + k))/z
		y = (2**(n + 2*k))/z

bsbRSR :: Int -> Int -> (Float,Float)
bsbRSR n' k' = (x,y)
	where
		n = intToFloat n'
		k = intToFloat k'
		z = (2**(2*n) + 2**k)
		x = (2**(2*n + (k/2)))/z
		y = (2**(n + k))/z

bsbRSL :: Int -> Int -> (Float,Float)
bsbRSL n' k' | (2 * n) >= k = (x,y)
	where
		n = intToFloat n'
		k = intToFloat k'
		x = 2**(k/2)
		y = (2**n) - (sqrt (2 ** (2 * n) - 2 ** k))
bsbRSL _ _ = (0,0)

trapezBSBP :: Int -> (Float,Float)
-- trapezBSB i < 0 = 
trapezBSBP 1 = (4,4)
trapezBSBP 2 = bsbRSL 2 3
trapezBSBP 3 = (2,2)
trapezBSBP 4 = bsbRSL 1 3
trapezBSBP 5 = bsbRSR 2 3
trapezBSBP 6 = bsbRR 1 2
trapezBSBP 7 = bsbRSL 2 3
trapezBSBP 8 = bsbRSR 2 2
trapezBSBP i | i > 0 = let
	ki = mod i 10
	mn5 h = (i - h) `div` 5
	ifl :: Int -> Int
	ifl k | or [k == 4,k == 9] = 1
	ifl k | or [k == 5, k == 0] = 2
	ifl k | or [k == 6, k == 1] = 3
	ifl k | or [k == 7, k == 2] = 4
	ifl k | or [k == 8, k == 3] = 5
	in case ifl ki of
		1 -> bsbRSL (((2+) . mn5) 9) 4
		2 -> bsbRSR (((2+) . mn5) 10) 3
		3 -> bsbRR 1 (((2+) . mn5) 11)
		4 -> bsbRSL (((2+) . mn5) 12) 3
		5 -> bsbRSR (((2+) . mn5) 13) 2
		_ -> error $ show (ifl ki)
trapezBSBP i = error $ show i

trapezBorder :: Float -> Picture
trapezBorder p = Color (PictureRGB8 255 0 0) $ ManyPicture 
	[ Line (V2 (2**p) (2**p)) (V2 (4**p) (4**p))
	, Line (V2 (4**p) (4**p)) (V2 (4**p) (2**p))
	, Line (V2 (4**p) (2**p)) (V2 (2**p) (2**p))
	]


anyTBSBP :: Int -> Int -> (V2 Float)
anyTBSBP p i = (\(x,y)->
	(V2 (x*2**(intToFloat p)) (y*2**(intToFloat p) )) ) (trapezBSBP $ abs i)

anyTBSBPI :: [(Int,Int)] -> [(V2 Float)]
anyTBSBPI = Pre.map (\(x,y)-> anyTBSBP x y)

genTBSBPIlist :: [(Int,Int)] -> [(V2 Float)]
genTBSBPIlist ((x,y):l) | (x > 0) || (y > 0) = [anyTBSBP x y] ++ (genTBSBPIlist l) --  (mod x pm) (mod y pi)
genTBSBPIlist _ = []

type GenTBSBPI = [(V2 Float)]
type GenTBSBPIAdj = EventAdj GenTBSBPI
type GenTBSBPIAdjointM = ElemAdjointM GenTBSBPIAdj
type GenTBSBPIAdjointW = ElemAdjointW GenTBSBPIAdj

type instance SysMonad (GenTBSBPIAdj) = IO
type instance SysComonad (GenTBSBPIAdj) = Store StdGen

genTBSBPIlistAdjPic :: GenTBSBPIAdjointM [Picture]
genTBSBPIlistAdjPic = do
	lp <- getEventAdjM (Proxy @GenTBSBPI)
	return $ listPointToLine lp
{-
type JoingAdj a b = VarAdj (Joing a b)

--instance System (Joing a b) where
--type instance SysAdjF (JoingAdj a b) = ElemAdjF (JoingAdj a b)
--type instance SysAdjG (JoingAdj a b) = ElemAdjG (JoingAdj a b) 
type instance SysMonad (JoingAdj a b) = IO
type instance SysComonad (JoingAdj a b) = Store StdGen	
-}
joingV2 :: SysAdjMonad (GenTBSBPIAdj :##: (JoingAdj (V2 Float) Picture)) Picture
joingV2 = () & cCompSysAdjM (Proxy @(GenTBSBPIAdj,(JoingAdj (V2 Float) Picture))) 
	(const $ getEventSysAdjM (Proxy @GenTBSBPI)) (fmap ManyPicture . joingSysMN (Proxy @Picture) 50 . Vec.fromList)

type instance SysMonad (VarAdj Repos) = IO
type instance SysComonad (VarAdj Repos) = Store StdGen
type instance SysMonad (VarAdj Rotation) = IO
type instance SysComonad (VarAdj Rotation) = Store StdGen

joingV2PosRot :: SysAdjMonad 
	((GenTBSBPIAdj :##: 
	(JoingAdj (V2 Float) Picture)) :##: (
	VarAdj Repos :##: 
	VarAdj Rotation)
	) Picture
joingV2PosRot = () & cCompSysAdjM 
	(Proxy @(GenTBSBPIAdj :##: (JoingAdj (V2 Float) Picture)
		, (VarAdj Repos :##: VarAdj Rotation)))
	(const joingV2)
	(liftEAdj (Proxy @(VarAdj Repos :##: VarAdj Rotation)) . compReposRotatAdj)

jV2PosRotMul :: (Picture -> SysAdjMonad (GenTBSBPIAdj :##: 
		(JoingAdj (V2 Float) Picture))
		Picture) 
	-> Float 
	-> SysAdjMonad 
		((GenTBSBPIAdj :##: 
		(JoingAdj (V2 Float) Picture)) :##: (
		VarAdj Repos :##: 
		VarAdj Rotation)
		) Picture
jV2PosRotMul fm vm = () & cCompSysAdjM 
	(Proxy @(GenTBSBPIAdj :##: (JoingAdj (V2 Float) Picture)
		, (VarAdj Repos :##: VarAdj Rotation)))
	(const ((>>= fm) $ fmap (multPic vm) joingV2) )
	(liftEAdj (Proxy @(VarAdj Repos :##: VarAdj Rotation)) . compReposRotatAdj)

listPointToLine :: [(V2 Float)] -> [Picture]
listPointToLine (x:y:l) = [Line x y] ++ (listPointToLine l)
listPointToLine _ = []

genListPointToLine :: [(Int,Int)] -> [Picture]
genListPointToLine li = listPointToLine $ genTBSBPIlist li

-- Test translate 500 500 $trapezBorder 3

drowLPAdjRand :: String -> IO ()
drowLPAdjRand n = do
	l <- genRandListZip 2 20
	vp <- extractL <$> (runSysAdj @((GenTBSBPIAdj :##: 
		(JoingAdj (V2 Float) Picture)) :##: (
		VarAdj Repos :##: 
		VarAdj Rotation)) (jV2PosRotMul (return . triangleRotation . reverseXYFull . triangleRotation) 4) )
			( Comp1 $ fmap ( const $ Comp1 
				( env (Joing 
					{ joingNumObj = 299
					, joingNumApp = 4
					, joingFun = \v-> ManyPicture $! ([Line (Vec.head v) (Vec.last v)] ++) $ Vec.ifoldr (f v) [] v
					}) 
					(tell $ genTBSBPIlist $ Pre.take 300 l)
				) )
				$ (Comp1
				(env (Rotation 0) (env (Repos $ V2 (500) (500)) ()) )
				)
			)
	savePicture (drowPic vp)
		n 1000 1000
	where
		f :: Vec.Vector (V2 Float) -> Int -> V2 Float -> [Picture] -> [Picture]
		f v i p lp = (do
			p2 <- maybeToList $ v Vec.!? (i+1)	
			return $ Line p p2
			) ++ lp 

triangleRotatTest ::  String -> IO ()
triangleRotatTest n = do
	l <- genRandListZip 3 20
	savePicture (translate 500 500 $ drowPic $ triangleRotation $ reverseXYFull $ powPicN [2] $ triangleRotation $
		ManyPicture $
		Pre.take 20 $ genListPointToLine l
		) n 1000 1000
	
genRandListZip :: Int -> Int ->  IO [(Int,Int)]
genRandListZip powI pointI = do
	s <- initStdGen
	let l1 = randomRs (1,powI)  s
	s2 <- initStdGen
	let l2 = randomRs (1,pointI) s2
	return $ Pre.zip l1 l2

drowLPAdj :: String -> IO ()
drowLPAdj n = do
	l <- genRandListZip 3 20
	--savePicture (translate 250 250 $ drowPic $ Line (0,0) (100,100) ) "drowLinePow" 500 500   
	savePicture (drowPic $ extractL $ (\f->f $ Comp1
			(env (Rotation 30) (env (Repos $ V2 (500) (500)) ()) ) 
		) $ runEAdj @(VarAdj Repos :##: VarAdj Rotation) $ genPicEAdj 300 l) n 1000 1000

genPicEAdj :: Int -> [(Int,Int)] -> ElemAdjointM (VarAdj Repos :##: VarAdj Rotation) Picture
genPicEAdj i l = compReposRotatAdj $ ManyPicture $ 
		genListPointToLine $ Pre.take i l

drowLinePow :: String -> IO ()
drowLinePow n = do
	s <- initStdGen
	let l1 = randomRs (1,3)  s
	s2 <- initStdGen
	let l2 = randomRs (1,22) s2
	--savePicture (translate 250 250 $ drowPic $ Line (0,0) (100,100) ) "drowLinePow" 500 500   
	savePicture (translate 500 500 $ drowPic $ 
		-- (\x-> ManyPicture [(reverseX x),(reverseY x),(reverseXY x),x]) $ 
			(\x-> ManyPicture [reverseXY x,x]) $ 
		ManyPicture $
		(Pre.take 20 $ genListPointToLine $ Pre.zip l1 l2)
		) n 1000 1000

{-
testBox = saveCorePicGen
	(CorePicGen 
		{ wibthCPG = First $ Just $ 1000
		, hightCPG = First $ Just $ 1000
		}
	)
	(liftA2 (\x y->(x,y)) [0..1000] [0..1000])
	( {-intersecSysGPMMap $-} ((sysGenPicM) =<<) $ foldToAltSys $
	fmap (translate 500 500) $ 
	join
	[ boxLine 8 16
	, manyPowCircleSq 8 16
	, join $ manyPowCircleLine 4 8
	] ) 
	"testPicBox" 
	1000 
	1000
-}
