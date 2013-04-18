module MLens where

-- based on https://gist.github.com/arkeet/4295507 by arkeet

import Control.Applicative
import Control.Lens
import Control.Lens.Internal
import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State
import Data.Foldable
import Data.IORef
import Data.Pointed
import Data.Traversable
import Data.Tuple
 
class (Traversable t) => Optional t where
  inspect :: (Functor f, Pointed f) => (a -> f b) -> (t a -> f (t b))
  inspect f = ifApplicableP . fmap f

  ifApplicableP :: (Functor f, Pointed f) => t (f a) -> f (t a)
  ifApplicableP = inspect id

  ifApplicableM :: (Monad m) => t (m a) -> m (t a)
  ifApplicableM = unwrapMonad . ifApplicableP . fmap WrapMonad

instance Optional Mutator where
  ifApplicableP = fmap Mutator . runMutator

instance Foldable (Accessor r) where
  foldr _ z _ = z

instance Traversable (Accessor r) where
  sequenceA = pure . coerce

instance Optional (Accessor r) where
  ifApplicableP = point . coerce

mviews :: Monad m
       => (a -> r)
       -> ((a -> Accessor r b) -> m (Accessor r u))
       -> m r
mviews f x = liftM runAccessor $ x (Accessor . f)
 
mview :: Monad m
      => ((a -> Accessor a b) -> m (Accessor a u))
      -> m a
mview x = mviews id x
 
mover :: Monad m
      => ((a -> Mutator b) -> m (Mutator u))
      -> (a -> b) -> m u
mover x f = liftM runMutator $
  x (Mutator . f)
 
infixr 4 >%~
(>%~) :: Monad m => ((a -> Mutator b) -> m (Mutator u)) -> (a -> b) -> m u
(>%~) = mover
 
 
returnL :: (Monad m, Functor f) => s -> (s -> f t) -> m (f t)
returnL a k = return (k a)
 
stateL :: (MonadState s m, Optional f) => (s -> f s) -> m (f ())
-- stateL k = state $ \s -> (fmap (const ()) (k s), l s)
stateL k = do
  s <- get
  let fs = k s
  let puts = fmap put fs
  ifApplicableM puts

readerL :: (MonadReader a m, Gettable f) => (a -> f b) -> m (f u)
readerL k = reader $ \r -> coerce (k r)

iorefL :: (MonadIO m, Optional f) => IORef s -> (s -> f s) -> m (f ())
iorefL ref = liftIO . atomicModifyIORef ref . (swap .) . runState . stateL

 
testReturn = runIdentity $ do
  x <- mview $ returnL (0,'a') . _1
  y <- returnL (0,'a') . _2 >%~ succ
  return (x,y)
  -- (0,(0,'b'))

testReader = flip runReader 0 $ do
  x <- mview readerL
  return x
  -- 0
 
testState = flip runState (0,0) $ do
  x <- mview $ stateL . _1
  y <- mview $ stateL . _2
  stateL . _2 >%~ (+2)
  z <- mview $ stateL . _2
  return (x,y,z)
  -- ((0,0,2),(0,2))

testIORef :: IO (Int, Int)
testIORef = do
  ref <- newIORef 0
  x <- mview $ iorefL ref
  iorefL ref >%~ (+2)
  y <- mview $ iorefL ref
  return (x,y)
  -- (0,2)
