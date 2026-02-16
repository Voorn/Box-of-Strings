module Main where

import Event
--import Display 

--import Graphics.Gloss

-- ============================
-- KEY INPUT
-- ============================

-- Whether to put into fullscreen mode or windowed mode
fullscreen :: Bool 
fullscreen = False

-- Application is made in a 3:2 ratio. Set the height below, or ste to Nothing for autoscaling
screenheight :: Maybe Int
screenheight = Just 960


main :: IO ()
main = playLoad fullscreen screenheight