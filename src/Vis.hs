
module Vis
  (
    RendIO, Appearance(..), Shape(..), Size, Color
  , SDL.Window, SDL.Renderer
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
draw appear = do
  rend <- get
  original <- SDL.get (SDL.rendererDrawColor rend)
  setDrawColor (appearanceColor appear) rend
  drawShape (mapShape fromIntegral $ appearanceShape appear) rend
  SDL.rendererDrawColor rend $= original

setDrawColor :: MonadIO m => Color -> Renderer -> m ()
setDrawColor color rend = SDL.rendererDrawColor rend $= withRGB (\r g b -> V4 r g b 255) color

mapShape :: (a -> b) -> Shape a -> Shape b
mapShape f (Rectangle (x,y) w h) = Rectangle (f x, f y) (f w) (f h)

drawShape :: MonadIO m => Shape CInt -> Renderer -> m ()
drawShape (Rectangle (x,y) w h) rend = SDL.fillRect rend (Just $ SDL.Rectangle (SDL.P (V2 x y)) (V2 w h))

drawScene :: [Appearance] -> RendIO ()
drawScene shape = get >>= SDL.clear >> mapM_ draw shape >> update

update :: RendIO ()
update = get >>= SDL.present

withVis :: (SDL.Window -> RendIO a) -> String -> (Int,Int) -> (Int,Int) -> IO ()
withVis f header phydim logdim = setup header phydim logdim >>= uncurry (\window -> evalStateT (f window >> finish window))

setup :: (MonadIO m) => String -> (Int,Int) -> (Int,Int) -> m (SDL.Window, SDL.Renderer)
setup header (phyw,phyh) (logw,logh) = do
  SDL.initialize [SDL.InitVideo]
  window <- SDL.createWindow (pack header) windowConfig 
  rend <- SDL.createRenderer window (-1) renderConfig
  SDL.rendererLogicalSize rend $= (Just . fmap fromIntegral $ V2 logw logh)
  return (window, rend)
  where
    windowConfig = SDL.defaultWindow{ SDL.windowInitialSize = fromIntegral <$> V2 phyw phyh
                                    , SDL.windowPosition = SDL.Centered}
    renderConfig = SDL.RendererConfig{ SDL.rendererType = SDL.AcceleratedRenderer
                                     , SDL.rendererTargetTexture = False}

waitForQuit :: SDL.Event -> RendIO ()
waitForQuit (SDL.Event _ (SDL.WindowClosedEvent _)) = return ()
waitForQuit _ = SDL.waitEvent >>= waitForQuit

finish :: Window -> RendIO ()
finish window = do
  SDL.waitEvent >>= waitForQuit  
  SDL.destroyRenderer =<< get
  SDL.destroyWindow window
  SDL.quit
