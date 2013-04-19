{-# LANGUAGE Rank2Types #-}
module MLens where

-- Lenses of a sort that access the implicit state or other data kept by a
-- monad.

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

-- A container like 'Traversable', but promises to contain at most one element. 
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

-- Lenses into implicit data, can be both read and written, and changes are
-- preserved through binds.
--
-- 1) You get back what you put in:
--
-- @
-- 'MLens.mset' l b >> 'MLens.mview' l  returns  b
-- @
--
-- 2) Putting back what you got doesn't change anything:
--
-- @
-- 'MLens.mview' l >>= 'MLens.mset' l  ~~~  return ()
-- @
--
-- 3) Setting twice is the same as setting once:
--
-- @
-- 'MLens.mset' l b >> 'MLens.mset' l c  ~~~  'MLens.set' l c
-- @
type MLens m a b = forall f. Optional f => (a -> f b) -> m (f ()) 
type MLens' m a = MLens m a a

-- Setters of implicit data.  Changes are again preserved across binds.
--
-- 1) identity law:
--
-- @
-- 'MLens.mover' l id  ~~~  return ()
-- @
--
-- 2) composition law:
--
-- @
-- 'MLens.mover' l f >> 'MLens.mover' l g  ~~~  'MLens.mover' l (g . f)
-- @
type MSetter m a b = forall f. Settable f => (a -> f b) -> m (f ())
type MSetter' m a = MSetter m a a
type AMSetter m a b u = (a -> Mutator b) -> m (Mutator u)

-- Getters of implicit data.  Similar to how plain getters are plain functions,
-- these are basically the same as arbitrary actions of type 'm a'.
type MGetter m a = forall f u. Gettable f => (a -> f a) -> m (f u)
type MGetting r m a u = (a -> Accessor r a) -> m (Accessor r u)

-- NOTE: Basically all this 'u' stuff could be got rid of at the expense of
--       losing 'returnL'.

-- Monadic form of 'views'.
mviews :: Monad m => (a -> r) -> MGetting r m a u -> m r
mviews f l = liftM runAccessor $ l (Accessor . f)

-- Monadic form of 'view'. 
mview :: Monad m => MGetting a m a u -> m a
mview l = mviews id l

-- Monadic form of 'over'. 
mover :: Monad m => AMSetter m a b u -> (a -> b) -> m u
mover l f = liftM runMutator $ l (Mutator . f)

-- Monadic form of 'set'.
mset :: Monad m => AMSetter m a b u -> b -> m u
mset l x = mover l (const x)

-- Infix form of 'mviews'.  Named for its similarity to application and '<$>'.
infixr 4 >$
(>$) :: Monad m => (a -> r) -> MGetting r m a u -> m r
(>$) = mviews
 
infixr 4 >%=
(>%=) :: Monad m => AMSetter m a b u -> (a -> b) -> m u
(>%=) = mover
 
infixr 4 >.=
(>.=) :: Monad m => AMSetter m a b u -> b -> m u
(>.=) = mset
 

-- NOTE: this is interesting, but it's not an MLens 
returnL :: (Monad m, Functor f) => s -> (s -> f t) -> m (f t)
returnL a k = return (k a)

-- I kind of want to call this one 'this'.
stateL :: (MonadState s m, Optional f) => (s -> f s) -> m (f ())
stateL k = do
  s <- get
  let fs = k s
  let puts = fmap put fs
  ifApplicableM puts

-- and this one 'env'.
readerL :: (MonadReader a m, Gettable f) => (a -> f b) -> m (f u)
readerL k = reader $ \r -> coerce (k r)

-- This only truly follows the MLens laws if the underlying IORef is only
-- visible to a single thread--otherwise, euqivalent sequences can be
-- distinguished by intermediate writes they make.  If you really need a
-- lens into state visible from multiple threads at once, probably STM is
-- your best way to do it.
iorefL :: (MonadIO m, Optional f) => IORef s -> (s -> f s) -> m (f ())
iorefL ref = liftIO . atomicModifyIORef ref . (swap .) . runState . stateL

 
testReturn = runIdentity $ do
  x <- mview $ returnL (0,'a') . _1
  y <- returnL (0,'a') . _2 >%= succ
  return (x,y)
  -- (0,(0,'b'))

testReader = flip runReader 0 $ do
  x <- mview readerL
  return x
  -- 0
 
testState = flip runState (0,0) $ do
  x <- mview $ stateL . _1
  y <- mview $ stateL . _2
  stateL . _2 >%= (+2)
  z <- mview $ stateL . _2
  return (x,y,z)
  -- ((0,0,2),(0,2))

testIORef = do
  ref <- newIORef 0
  x <- mview $ iorefL ref
  iorefL ref >%= (+2)
  y <- mview $ iorefL ref . to show
  return (x,y)
  -- (0,2)
