{-# Language TypeFamilies, DeriveAnyClass, TypeApplications, BangPatterns #-}

module Data.PicGen.Core where

import Prelude as Pre

import GHC.Generics
import GHC.Float

import Codec.Picture

import Control.Applicative as App
import Control.Monad.Logic
import Control.Monad.Reader as Re
import Control.Monad.Writer as Wr

import Control.Comonad.Trans.Traced as Tr
import Control.Comonad.Trans.Env as En
import Control.Comonad
import Control.Comonad.Trans.Class

import Data.List.NonEmpty as NE
import Data.Word
import Data.Proxy 
import Data.Function

import Data.Maybe

import Linear.Metric
import Linear.V2

import Data.Map.Lazy as Ml
import Data.Functor.Adjunction

import Control.Core.System

testPic = savePicture (ray 2 (0,0) (100,50) )  "testPic" 500 500

data PictureRGB8 = PictureRGB8 
	{ redSum :: Sum Word8
	, greenSum :: Sum Word8
	, blueSum :: Sum Word8
	} deriving (Eq)

instance Semigroup PictureRGB8 where
  (<>) (PictureRGB8 x1 y1 z1) (PictureRGB8 x2 y2 z2) = PictureRGB8 (x1 <> x2) (y1 <> y2) (z1 <> z2)

instance Monoid PictureRGB8 where
  mempty = PictureRGB8 mempty mempty mempty 

type GenPictureRGB8 = (Int -> Int -> PictureRGB8)

savePicture :: GenPictureRGB8 -> String -> Int -> Int -> IO ()
savePicture f s x y = saveBmpImage s $ ImageRGB8 $ generateImage 
	(\t1 t2-> (\(PictureRGB8 (Sum w1) (Sum w2) (Sum w3))->PixelRGB8 w1 w2 w3) $ f t1 t2 ) x y

-- Primary paterns pic generation
{-
line :: (Int,Int) -> (Int,Int) -> GenPictureRGB8
line (x1,y1) (x2,y2) = (\x y-> if (div (y - y1) (y2 - y1) == div (x - x1) (x2 - x1)) -- || ()   -- (abs (x1 - x) + abs (x2 - x) == abs (x1 -x2)) && (abs (y1 - y) + abs (y2 - y) == abs (y1 - y2) ) && ( )
	then PictureRGB8 255 255 255 -- 1 0 0
	else PictureRGB8 0 0 0circle (0,0)
	)
-}

ray :: Float -> (Float,Float) -> (Float,Float) -> GenPictureRGB8
ray h (x1,y1) (x2,y2) = (\x y-> let
	xv = x2 - x1
	yv = y2 - y1
	xv2 = (int2Float x) - x1 
	yv2 = (int2Float y) - y1
	xv3 = x2 - (int2Float x)
	yv3 = y2 - (int2Float y)
	in if (quadrance (project (V2 xv yv) (V2 xv2 yv2)) - quadrance (V2 xv2 yv2) <= h) && (quadrance (project (V2 xv yv) (V2 xv2 yv2)) - quadrance (V2 xv2 yv2) >= (-h)) 
	then PictureRGB8 255 255 255 -- 1 0 0
	else PictureRGB8 0 0 0
	)

line :: Float -> (Float,Float) -> (Float,Float) -> GenPictureRGB8
line h (x1,y1) (x2,y2) = (\x y-> let
	xv = x2 - x1
	yv = y2 - y1
	xv2 = (int2Float x) - x1 
	yv2 = (int2Float y) - y1
	xv3 = x2 - (int2Float x)
	yv3 = y2 - (int2Float y)
	in if (quadrance (project (V2 xv yv) (V2 xv2 yv2)) - quadrance (V2 xv2 yv2) <= h) && (quadrance (project (V2 xv yv) (V2 xv2 yv2)) - quadrance (V2 xv2 yv2) >= (-h)) && 
		(quadrance (V2 xv2 yv2) <= quadrance (V2 xv yv)) && (quadrance (V2 xv3 yv3) <= quadrance (V2 xv yv))
	then PictureRGB8 255 255 255 -- 1 0 0
	else PictureRGB8 0 0 0
	)
{-
s = a*b/2
(y - y1)/(y2 - y1) = (x - x1)/(x2 - x1)
y = x a - b

xv = x2 - x1
yv = y2 - x1

sq(x2^2 + y2^2) = r2^2
sq(y1^2 + x1^2) = r1^2
sq(xv^2+yv^2) = rv^2
sq((x1 - x ) )

lineIx :: (Int,Int) -> (Int,Int) -> [(Int,Int)]
lineIx (x1,y1) (x2,y2) = join $ liftA (\x y-> if (abs (x1 - x) + abs (x2 - x) == abs (x1 -x2)) && (abs (y1 - y) + abs (y2 - y) == abs (y1 - y2) )
	then [(x,y)]
	else []
 ) [x1,x1+1..x2] [y1,y1+1..y2]
-}
circle :: (Int,Int) -> Int -> GenPictureRGB8
circle (x0,y0) r = (\x y-> if ((x - x0)^2 + (y - y0)^2 > (r-1)^2 ) && ((x - x0)^2 + (y - y0)^2 < (r + 1)^2 )
	then PictureRGB8 255 255 255
	else PictureRGB8 0 0 0
	)
{-
circleIx :: (Int,Int) -> Int -> [(Int,Int)]
circleIx (x0,y0) r = join $ liftA (\x y-> if ((x - x0)^2 + (y - y0)^2 > (r-1)^2 ) && ((x - x0)^2 + (y - y0)^2 < (r + 1)^2 )
	then [(x,y)]
	else []
	) [x0-r-1..x0+r+1] [y0-r-1..y0+r+1]
-}
mapColor :: (PictureRGB8 -> PictureRGB8) -> GenPictureRGB8 -> GenPictureRGB8
mapColor f g = \ x y -> f $ g x y

mapPosition :: (Int -> Int -> (Int,Int)) -> GenPictureRGB8 -> GenPictureRGB8
mapPosition f g = \ x y -> (\(x1,y1)-> g x1 y1) $ f x y

translate :: Int -> Int -> GenPictureRGB8 -> GenPictureRGB8
translate x y = mapPosition (\ x1 y1->(x1 - x,y1 - y))

data Picture = Line {- Float -} (Float,Float) (Float,Float)
	| Circle (Float,Float) Float
	| ManyPicture [Picture]
	| Color PictureRGB8 Picture

mapPic :: (Picture -> Picture) -> Picture -> Picture
mapPic f (ManyPicture l) = ManyPicture $ fmap (mapPic f) l
mapPic f p = f p

drowPic :: Picture -> GenPictureRGB8
drowPic (Line (x1,y1) (x2,y2)) = line 0.5 (x1,y1) (x2,y2) -- (round x1,round y1) (round x2,round y2) -- (ceiling x1,ceiling y1) (ceiling x2,ceiling y2)
drowPic (Circle (x,y) r) = circle (round x,round y) (round r)
drowPic (ManyPicture l) =  foldMap drowPic l
drowPic (Color c p) = mapColor (\c2->if c2 /= (PictureRGB8 0 0 0) then c else c2) $ drowPic p

reverseX :: Picture -> Picture
reverseX = mapPic f
	where
		f (Line (x1,y1) (x2,y2)) = Line (-x1,y1) (-x2,y2)
		f (Circle (x,y) r) = Circle (-x,y) r
		f (ManyPicture l) = ManyPicture $ fmap (mapPic reverseX) l
		f (Color c l) = Color c $ mapPic reverseX l

reverseY :: Picture -> Picture
reverseY = mapPic f
	where
		f (Line (x1,y1) (x2,y2)) = Line (x1,-y1) (x2,-y2)
		f (Circle (x,y) r) = Circle (x,-y) r
		f (ManyPicture l) = ManyPicture $ fmap (mapPic reverseY) l
		f (Color c l) = Color c $ mapPic reverseY l

reverseXY :: Picture -> Picture
reverseXY = reverseX . reverseY

reverseD :: Picture -> Picture
reverseD = reverseXY . mapPic f
	where
		f (Line (x1,y1) (x2,y2)) = Line (-x1,-y1) (-x2,-y2)
		f (Circle (x,y) r) = Circle (-x,-y) r
		f (ManyPicture l) = ManyPicture $ fmap (mapPic reverseY) l
		f (Color c l) = Color c $ mapPic reverseY l
-- f2 x = (\y-> (y ^-^ x) ) $ project (0.5,0.5) x

powPic :: Float -> Picture -> Picture
powPic p = mapPic f
	where
		f (Line (x1,y1) (x2,y2)) = Line (x1**p,y1**p) (x2**p,y2**p)
		f (Circle (x,y) r) = Circle (x**p,y**p) (r**p)
		f (ManyPicture l) = ManyPicture $ fmap (mapPic (powPic p)) l
		f (Color c l) = Color c $ mapPic (powPic p) l

-- get intersec points 

intersecPoint :: GenPictureRGB8 -> GenPictureRGB8 -> Int -> Int -> [(Int,Int)]
intersecPoint g1 g2 x1 x2 = join $ forM (Pre.zip [0 .. x1] [0 .. x2]) (\(x,y)->do
	let c1 = g1 x y
	let c2 = g2 x y
	if (c1 /= mempty) && (c2 /= mempty) 
		then return (x,y)
		else App.empty 
	) 

-- patern combination 

data CorePicGen = CorePicGen 
	{ wibthCPG :: First Int
	, hightCPG :: First Int
	} deriving (Monoid, Semigroup)

type instance SysAdjF CorePicGen = (Env CorePicGen)
type instance SysAdjG CorePicGen = (Reader CorePicGen)

type instance SysMonad CorePicGen = Logic
type instance SysComonad CorePicGen = NonEmpty

runCorePicGen :: CorePicGen -> SysAdjMonad CorePicGen a -> [a] 
runCorePicGen cpg msam = fmap extractL $ (\x-> observeAll $ runReader x cpg) $ runSysAdjMonad msam

saveCorePicGen :: CorePicGen -> SysAdjMonad CorePicGen (Int,Int,PictureRGB8) -> String -> Int -> Int -> IO ()
saveCorePicGen cpg msam nameF w h = (\x-> savePicture 
		(\z y-> maybe (PictureRGB8 0 0 0) id $ x Ml.!? (z,y) ) nameF w h
	) $ mconcat $ fmap (\(x,y,z)-> Ml.singleton (x,y) z) $ runCorePicGen cpg msam

saveCorePicGenDef :: SysAdjMonad CorePicGen (Int,Int,PictureRGB8) -> IO ()
saveCorePicGenDef s = saveCorePicGen
	(CorePicGen 
		{ wibthCPG = First $ Just 1000
		, hightCPG = First $ Just 1000
		}
	)
	s
	"defName"
	1000
	1000

sysGenPicM :: GenPictureRGB8 -> SysAdjMonad CorePicGen (Int,Int,PictureRGB8)
sysGenPicM gpRGB = do
	lp <- sysAdjMapMF (Proxy :: Proxy (CorePicGen) ) 
		(\(EnvT a b)-> EnvT a (
			fmap (const 
				(Pre.zip [0..(fromJust $ getFirst $ wibthCPG a)] [0..(fromJust $ getFirst $ hightCPG a)])
			) b)
		) -- (fmap (snd . extract . runWriterT) . duplicateL)
	liftSysM $ join $ fmap msum $ forM lp (\ (x,y) -> do
		return $ return (x,y,gpRGB x y)
		)

getListIxM :: SysAdjMonad CorePicGen [(Int,Int)]
getListIxM = sysAdjMapMF (Proxy :: Proxy (CorePicGen) ) 
		(\(EnvT a b)-> EnvT a (
			fmap (const 
				(Pre.zip [0..(fromJust $ getFirst $ wibthCPG a)] [0..(fromJust $ getFirst $ hightCPG a)])
			) b)
		)

getListIxW :: SysAdjComonad CorePicGen x -> SysAdjComonad CorePicGen [(Int,Int)]
getListIxW = sysAdjMapWG  
		(\mr-> mr >> Re.ask >>= (\a-> return $
				Pre.zip [0..(fromJust $ getFirst $ wibthCPG a)] [0..(fromJust $ getFirst $ hightCPG a)]
		))
getMap :: Ord k 
	=> SysAdjMonad CorePicGen (k,a) -> SysAdjMonad CorePicGen (Map k [a])
getMap = mapSysM (return. Pre.foldr (unionWith (++)) Ml.empty . fmap (\(k,a)->Ml.singleton k [a]) )

intersecSysGPMMap :: SysAdjMonad CorePicGen (Int,Int,PictureRGB8) -> SysAdjMonad CorePicGen (Int,Int,PictureRGB8)
intersecSysGPMMap = mapSysM (join . fmap (foldToAlt . mapWithKey (\ (x,y) a -> (\z->(x,y,z)) $ Pre.head a))) . 
	fmap ( Ml.filter ((> 1) . Pre.length)) . getMap . fmap (\(x,y,z)->((x,y),z))

foldToAltSys :: Foldable f => f a -> SysAdjMonad CorePicGen a
foldToAltSys f = mapSysM (>> (foldToAlt f)) $ return ()

foldToAlt :: (Foldable f, Alternative m) => f a -> m a
foldToAlt = Pre.foldr (\a m-> (pure a) <|> m) App.empty

intersecSysGPMApp :: SysAdjMonad CorePicGen (Int,Int,PictureRGB8) -> SysAdjMonad CorePicGen (Int,Int,PictureRGB8)
intersecSysGPMApp (!m) = mapSysM (join . fmap (maybe App.empty return)) $ liftA2 (\ x y-> if x == y 
	then Just x
	else Nothing
	) m m

intersecSysGPM :: SysAdjMonad CorePicGen (Int,Int) -> SysAdjMonad CorePicGen (Int,Int)
intersecSysGPM = mapSysM (\m-> m >>- (\(x,y)->do
	--lp <- liftSysM $ many (unSysAdjMonad m)
	(x1,y1) <- m
	if (x == x1) && (y == y1)
			then return (x,y)
			else App.empty
	))
{-	liftSysM $ join  $ fmap msum $ (fmap . fmap) return $ forM lp (\(x1,y1)-> do
		if (x == x1) && (y == y1)
			then return (x,y)
			else lift $ empty
		)
	)
-}
sysGenPicW :: SysAdjComonad CorePicGen GenPictureRGB8 -> NonEmpty (Int,Int,PictureRGB8)
sysGenPicW = join . fmap (NE.fromList) . lowerSysW . extract . extend (\x-> (fmap (\(a,b)-> (a,b,(extract x) a b ))) <$> getListIxW x)
--sysGenPicW = join $ fmap (\(x,y)-> NE.fromList $ fmap (\(x1,y1)-> (x1,y1,x x1 y1) ) y ) . lowerSysW . _a . sysAdjMapWG Tr.listen

genCoAndKleisly :: PCAKSysAdj CorePicGen GenPictureRGB8 (Int,Int,PictureRGB8)
genCoAndKleisly = arrowToPCAKSAarr (\ne-> liftSysM $ msum $ fmap return ne) sysGenPicW
