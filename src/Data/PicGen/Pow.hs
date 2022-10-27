{-# Language TypeFamilies, DeriveAnyClass, TypeApplications #-}

module Data.PicGen.Pow where

import Prelude as Pre
import Extra

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

import Data.List.NonEmpty as NE
import Data.Word
import Data.Proxy 
import Data.PicGen.Core

import Data.Functor.Adjunction

import Control.Core.System
{-
powsquare2 :: Int -> Int
powsquare2 i = ceiling $ (sqrt 2 :: Float) ^ i
pow2 i = 2 ^ i

boxToPowSq i = (line (x,x) (x,-x)) <> (line (x,-x) (-x,-x)) <> (line (-x,-x) (-x,x)) <> (line (-x,x) (x,x))
	where
		x = powsquare2 i 

boxToPow i = (line (x,x) (x,-x)) <> (line (x,-x) (-x,-x)) <> (line (-x,-x) (-x,x)) <> (line (-x,x) (x,x))
	where
		x = pow2 i 

boxLine i i2 = fmap (\j->boxToPowSq j ) [i..i2]

powCircleSq i = circle (0,0) (powsquare2 i)

powCircleLine i i2 x y = fmap (\j->circle (x * (pow2 i), y * (pow2 i)) (pow2 i) ) [i..i2]

manyPowCircleSq i i2 = fmap (\j->powCircleSq j ) [i..i2] -- mconcat

manyPowCircleLine i i2 = (fmap (\j->powCircleLine j j 1 0) $ [i..i2] ) <>
	(fmap (\j->powCircleLine j j 0 1 ) $ [i..i2]) <>
	(fmap (\j->powCircleLine j j 0 (-1)) $ [i..i2]) <>
	(fmap (\j->powCircleLine j j (-1) 0) $ [i..i2])
-}
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
	[ Line (2**p,2**p) (4**p,4**p)
	, Line (4**p,4**p) (4**p,2**p)
	, Line (4**p,2**p) (2**p,2**p)
	]


anyTBSBP :: Int -> Int -> (Float,Float)
anyTBSBP p i = (\(x,y)->
	(x*2**(intToFloat p), y*2**(intToFloat p) ) ) (trapezBSBP $ abs i)

anyTBSBPI :: [(Int,Int)] -> [(Float,Float)]
anyTBSBPI = Pre.map (\(x,y)-> anyTBSBP x y)

genTBSBPIlist :: [(Int,Int)] -> [(Float,Float)]
genTBSBPIlist ((x,y):l) | (x > 0) || (y > 0) = [anyTBSBP x y] ++ (genTBSBPIlist l) --  (mod x pm) (mod y pi)
genTBSBPIlist _ = []

listPointToLine :: [(Float,Float)] -> [Picture]
listPointToLine (x:y:l) = [Line x y] ++ (listPointToLine l)
listPointToLine _ = []

genListPointToLine :: [(Int,Int)] -> [Picture]
genListPointToLine li = listPointToLine $ genTBSBPIlist li

-- Test translate 500 500 $trapezBorder 3

drowLinePow :: String -> IO ()
drowLinePow n = do
	s <- initStdGen
	let l1 = randomRs (1,3)  s
	s2 <- initStdGen
	let l2 = randomRs (1,22) s2
	--savePicture (translate 250 250 $ drowPic $ Line (0,0) (100,100) ) "drowLinePow" 500 500   
	savePicture (translate 500 500 $ drowPic $ 
		-- (\x-> ManyPicture [(reverseX x),(reverseY x),(reverseXY x),x]) $ 
			(\x-> ManyPicture [reverseD x,x]) $ 
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
