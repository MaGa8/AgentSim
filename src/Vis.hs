
module Vis
  (
    RendIO, Appearance, Shape(..), Size, Color
  , draw, update, drawScene
  , setup, finish, withVis
  ) where

import Control.Monad.State

import Foreign.C.Types

import Data.Text(pack)
import SDL(Window, Renderer, ($=), V2(..), V3(..), V4(..))
import qualified SDL

type RendIO = StateT Renderer IO
type Size = Int
data Shape a = Rectangle{ getRectOff :: (a,a), getRectSpanx :: a, getRectSpany :: a }
type Color = (Int, Int, Int)
newtype Appearance = Appearance (Shape Int, Color)

appearanceShape :: Appearance -> Shape Int
appearanceShape (Appearance (shape,_)) = shape

appearanceColor :: Appearance -> Color
appearanceColor (Appearance (_,color)) = color

withRGB :: (Integral a) => (a -> a -> a -> c) -> Color -> c
withRGB f (r,g,b) = f (fromIntegral r) (fromIntegral g) (fromIntegral b)

draw :: Appearance -> RendIO ()
draw appear = get >>= (\rend -> setDrawColor (appearanceColor appear) rend >> drawShape (mapShape fromIntegral $ appearanceShape appear) rend)

setDrawColor :: MonadIO m => Color -> Renderer -> m ()
setDrawColor color rend = SDL.rendererDrawColor rend $= withRGB (\r g b -> V4 r g b 255) color

mapShape :: (a -> b) -> Shape a -> Shape b
mapShape f (Rectangle (x,y) w h) = Rectangle (f x, f y) (f w) (f h)

drawShape :: MonadIO m => Shape CInt -> Renderer -> m ()
drawShape (Rectangle (x,y) w h) rend = SDL.fillRect rend (Just $ SDL.Rectangle (SDL.P (V2 x y)) (V2 w h))

drawScene :: [Appearance] -> RendIO ()
drawScene shape =  mapM_ draw shape >> update

update :: RendIO ()
update = get >>= SDL.present

withVis :: (SDL.Window -> RendIO a) -> String -> Int -> Int -> RendIO ()
withVis f header w h = setup header w h >>= (\window -> f window >> finish window)

setup :: String -> Int -> Int -> RendIO SDL.Window
setup header w h = do
  SDL.initialize [SDL.InitVideo]
  window <- SDL.createWindow (pack header) windowConfig 
  put =<< SDL.createRenderer window (-1) renderConfig
  return window
  where
    windowConfig = SDL.defaultWindow{ SDL.windowInitialSize = fromIntegral <$> V2 w h
                                    , SDL.windowPosition = SDL.Centered}
    renderConfig = SDL.RendererConfig{ SDL.rendererType = SDL.AcceleratedRenderer
                                     , SDL.rendererTargetTexture = False}

finish :: Window -> RendIO ()
finish window = do
  SDL.destroyRenderer =<< get
  SDL.destroyWindow window
  SDL.quit
