module Main where

import Control.Concurrent (threadDelay)
import Control.Monad (unless, when)
import Sound.ProteaAudio

import Gloss.Display
import IO.Config

--import Morph
--import Par2
import Gloss.Screen
--import Display 

--import Graphics.Gloss

-- ============================
-- KEY INPUT
-- ============================

filepath :: String
filepath = "input"

-- Whether to put into fullscreen mode or windowed mode
fullscreen :: Bool 
fullscreen = False

darkmode :: Bool
darkmode = False

-- Application is made in a 3:2 ratio. Set the height below, or ste to Nothing for autoscaling
screenheight :: Maybe Int
screenheight = Nothing --Just 800

orient :: Orient
orient = LR

zoomOn :: Bool
zoomOn = True

soundOn :: Bool
soundOn = True

-- audio test

main :: IO ()
main = do
    settingConfig (filepath , darkmode , fullscreen , orient , zoomOn , soundOn) 
    >>= \(filepath' , darkmode' , fullscreen' , orient' , zoomOn' , soundOn') 
    -> playLoad fullscreen' Nothing darkmode' (filepath' , soundOn') orient' zoomOn'

--waitForPlayback :: IO ()
--waitForPlayback = do
--    activeCount <- soundActiveAll
--    when (activeCount > 0) $ do
--        threadDelay 100000  -- sleep for 0.1 seconds (100,000 microseconds)
--        waitForPlayback


    --do {
    --    sampleFromFile "guitar.mp3" 1 >>= \s -> soundPlay s 1 1 0 1 >>= \z -> soundActive z >>= \b -> print b;
    --    settingConfig (filepath , darkmode , fullscreen , orient , zoomOn) >>= \(filepath' , darkmode' , fullscreen' , orient' , zoomOn') -> playLoad fullscreen' Nothing darkmode' filepath' orient' zoomOn'
    --}