{-# LANGUAGE Rank2Types, MultiParamTypeClasses, FunctionalDependencies, FlexibleInstances, GADTs #-}
module ELens where

-- Lenses of a sort that access the implicit state or other data kept by a
-- monad.

-- based on https://gist.github.com/arkeet/4295507 by arkeet
--
-- and suggestions by edwardk

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

class (Monad m, Functor f) => Effectual m f | f -> m where
  -- don't know what's actually needed here
  lbind :: m a -> (a -> f b) -> f b
  rbind :: f a -> (a -> m b) -> f b

instance Monad m => Effectual m (WrappedMonad m) where
  lbind m f = WrapMonad $ m >>= (unwrapMonad . f)
  rbind t g = WrapMonad $ unwrapMonad t >>= g

instance Monad m => Effectual m (Effect m r) where
  lbind m f = effective $ m >>= (ineffective . f)
  rbind = const . (effective . ineffective) -- could just as well be unsafeCoerce

-- Lenses into implicit data, can be both read and written, and changes are
-- preserved through binds.
--
-- 1) You get back what you put in:
--
-- @
-- 'ELens.eset' l b >> 'ELens.eview' l  returns  b
-- @
--
-- 2) Putting back what you got doesn't change anything:
--
-- @
-- 'ELens.eview' l >>= 'ELens.eset' l  ~~~  return ()
-- @
--
-- 3) Setting twice is the same as setting once:
--
-- @
-- 'ELens.eset' l b >> 'ELens.eset' l c  ~~~  'ELens.set' l c
-- @
-- type ELens m s t a b = forall f. Optional f => (a -> f b) -> m (f ()) 
-- type ELens' m s a = Simple (ELens m) s a

-- Setters of implicit data.  Changes are again preserved across binds.
--
-- 1) identity law:
--
-- @
-- 'ELens.eover' l id  ~~~  return ()
-- @
--
-- 2) composition law:
--
-- @
-- 'ELens.eover' l f >> 'ELens.eover' l g  ~~~  'ELens.eover' l (g . f)
-- @
type ESetter m s t a b = forall f. (f ~ WrappedMonad m) => (a -> f b) -> m (f ())
type ESetter' m s a = Simple (ESetter m) s a
type AESetter m s t a b = LensLike (WrappedMonad m) s t a b

-- Getters of implicit data.  Similar to how plain getters are plain functions,
-- these are basically the same as arbitrary actions of type 'm a'.
type EGetter m s a = Action m s a
type EGetting m r s t a b = Acting m r s t a b

-- NOTE: Basically all this 'u' stuff could be got rid of at the expense of
--       losing 'returnL'.

-- Monadic form of 'views'.
eviews :: Monad m => (a -> r) -> EGetting m r s t a b -> (s -> m r)
eviews f l = getEffect . l (Effect . return . f)

-- Monadic form of 'view'. 
eview :: Monad m => EGetting m a s t a b -> (s -> m a)
eview l = eviews id l

-- Monadic form of 'over'. 
eover :: Monad m => AESetter m s t a b -> (a -> b) -> (s -> m t)
eover l f = liftM unwrapMonad $ l (WrapMonad . return . f)

-- Monadic form of 'set'.
eset :: Monad m => AESetter m s t a b -> b -> (s -> m t)
eset l x = eover l (const x)

-- Infix form of 'eview'.
infixr 4 ^!.
(^!.) :: Monad m => s -> EGetting m a s t a b -> m a
(^!.) = flip eview
 
infixr 4 !%~
(!%~) :: Monad m => AESetter m s t a b -> (a -> b) -> s -> m t
(!%~) = eover
 
infixr 4 !.~
(!.~) :: Monad m => AESetter m s t a b -> b -> s -> m t
(!.~) = eset
 

{-
-- NOTE: this is interesting, but it's not an ELens 
returnL :: (Monad m, Functor f) => s -> (s -> f t) -> m (f t)
returnL a k = return (k a)
-}

-- I kind of want to call this one 'this'.
stateL :: (MonadState a m, Effectual m f) => (a -> f a) -> (s -> f s)
stateL k = \x -> get `lbind` (\v -> k v `rbind` (\r -> put r >> return x))

-- and this one 'env'.
readerL :: (MonadReader a m) => EGetter m s a
readerL k = effective . (\_ -> ask >>= (ineffective . k))
-- reader $ \r -> coerce (k r)

-- This only truly follows the ELens laws if the underlying IORef is only
-- visible to a single thread--otherwise, euqivalent sequences can be
-- distinguished by intermediate writes they make.  If you really need a
-- lens into state visible from multiple threads at once, probably STM is
-- your best way to do it.
iorefL :: (MonadIO m, Effectual m f) => IORef a -> (a -> f a) -> (s -> f s)
iorefL ref = \k x -> liftIO (readIORef ref) `lbind`
                     (\v -> k v `rbind`
                     (\r -> liftIO (writeIORef ref r) >> return x))
  -- liftIO . atomicModifyIORef ref . (swap .) . runState . stateL
 
testReturn = runIdentity $ do
  x <- (0,'a') ^!. _1
  y <- (0,'a') & _2 !%~ succ
  return (x,y)
  -- (0,(0,'b'))

testReader = flip runReader 0 $ do
  x <- () ^!. readerL
  return x
  -- 0
 
testState = flip runState (0,0) $ do
  x <- () ^!. stateL . _1
  y <- () ^!. stateL . _2
  () & stateL . _2 !%~ (+2)
  z <- () ^!. stateL . _2
  return (x,y,z)
  -- ((0,0,2),(0,2))

testIORef :: IO (Int,String)
testIORef = do
  ref <- newIORef 0
  x <- () ^!. iorefL ref
  () & iorefL ref !%~ (+2)
  y <- () ^!. iorefL ref . to show
  return (x,y)
  -- (0,"2")
