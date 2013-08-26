{-| Runners and distributive laws for Proxy and FreeT.
-}

{-# LANGUAGE CPP, Rank2Types #-}

module Lifts (
    -- * ErrorT
    errorP,
    runErrorP,
    distErrorP,
    catchError,
    liftCatchError,
    errorF,
    runErrorF,
    distErrorF,

    -- * MaybeT
    maybeP,
    runMaybeP,
    distMaybeP,
    maybeF,
    runMaybeF,
    distMaybeF,

    -- * ReaderT
    readerP,
    runReaderP,
    distReaderP,
    readerF,
    runReaderF,
    distReaderF,

    -- * StateT
    stateP,
    runStateP,
    evalStateP,
    execStateP,
    distStateP,
    stateF,
    runStateF,
    evalStateF,
    execStateF,
    distStateF,

    -- * WriterT
    -- $writert
    writerP,
    runWriterP,
    execWriterP,
    distWriterP,
    writerF,
    runWriterF,
    execWriterF,
    distWriterF,

    -- * RWST
    rwsP,
    runRWSP,
    evalRWSP,
    execRWSP,
    distRWSP
{-
    rwsF,
    runRWSF,
    evalRWSF,
    execRWSF,
    distRWSF,
-}
    ) where

import Control.Monad.Trans.Class (lift)
import qualified Control.Monad.Trans.Error as E
import qualified Control.Monad.Trans.Maybe as M
import qualified Control.Monad.Trans.Reader as R
import qualified Control.Monad.Trans.State.Strict as S
import qualified Control.Monad.Trans.Writer.Strict as W
import qualified Control.Monad.Trans.RWS.Strict as RWS
import Data.Monoid (Monoid(mempty, mappend))
import Pipes.Internal
import qualified Control.Monad.Trans.Free as F

-- | Based on unsafeHoist, but for 'F.FreeT'
hoistF
    :: (Monad m, Functor f)
    => (forall x . m x -> n x) -> F.FreeT f m r -> F.FreeT f n r
hoistF nat = go
  where
    go m = F.FreeT (nat (do
        m' <- F.runFreeT m
        return (case m' of
            F.Pure r -> F.Pure r
            F.Free f -> F.Free (fmap go f))
      ))

-- | Wrap the base monad in 'E.ErrorT'
errorP
    :: (Monad m, E.Error e)
    => Proxy a' a b' b m (Either e r)
    -> Proxy a' a b' b (E.ErrorT e m) r
errorP p = do
    x <- unsafeHoist lift p
    lift $ E.ErrorT (return x)
{-# INLINABLE errorP #-}

-- | Run 'E.ErrorT' in the base monad
runErrorP
    :: (Monad m)
    => Proxy a' a b' b (E.ErrorT e m) r -> Proxy a' a b' b m (Either e r)
runErrorP = go
  where
    go p = case p of
        Request a' fa  -> Request a' (\a  -> go (fa  a ))
        Respond b  fb' -> Respond b  (\b' -> go (fb' b'))
        Pure    r      -> Pure (Right r)
        M          m   -> M (do
            x <- E.runErrorT m
            return (case x of
                Left  e  -> Pure (Left e)
                Right p' -> go p' ) )
{-# INLINABLE runErrorP #-}

-- | Pull 'E.ErrorT' outside of Proxy.  This is a monad morphism.
distErrorP
    :: (Monad m)
    => Proxy a' a b' b (E.ErrorT e m) r
    -> E.ErrorT e (Proxy a' a b' b m) r
distErrorP p = E.ErrorT (runErrorP p)
{-# INLINABLE distErrorP #-}

-- | Wrap the base monad in 'E.ErrorT'
errorF
    :: (Monad m, Functor f, E.Error e)
    => F.FreeT f m (Either e r)
    -> F.FreeT f (E.ErrorT e m) r
errorF p = do
    x <- hoistF lift p
    lift $ E.ErrorT (return x)
{-# INLINABLE errorF #-}

-- | Run 'E.ErrorT' in the base monad
runErrorF
    :: (Monad m, Functor f)
    => F.FreeT f (E.ErrorT e m) r -> F.FreeT f m (Either e r)
runErrorF = go
  where
    go m = F.FreeT (do
        x <- E.runErrorT (F.runFreeT m)
        return (case x of
            Left  e          -> F.Pure (Left e)
            Right (F.Pure r) -> F.Pure (Right r)
            Right (F.Free f) -> F.Free (fmap go f) ) )
{-# INLINABLE runErrorF #-}

-- | Pull 'E.ErrorT' outside of 'F.FreeT'.  This is a monad morphism.
distErrorF
    :: (Monad m, Functor f)
    => F.FreeT f (E.ErrorT e m) r -> E.ErrorT e (F.FreeT f m) r
distErrorF m = E.ErrorT (runErrorF m)
{-# INLINABLE distErrorF #-}

-- | Catch an error in the base monad
catchError
    :: (Monad m) 
    => Proxy a' a b' b (E.ErrorT e m) r
    -- ^
    -> (e -> Proxy a' a b' b (E.ErrorT f m) r)
    -- ^
    -> Proxy a' a b' b (E.ErrorT f m) r
catchError p0 f = go p0
  where
    go p = case p of
        Request a' fa  -> Request a' (\a  -> go (fa  a ))
        Respond b  fb' -> Respond b  (\b' -> go (fb' b'))
        Pure    r      -> Pure r
        M          m   -> M (E.ErrorT (do
            x <- E.runErrorT m
            return (Right (case x of
                Left  e  -> f  e
                Right p' -> go p' )) ))
{-# INLINABLE catchError #-}

-- | Wrap the base monad in 'M.MaybeT'
maybeP
    :: (Monad m)
    => Proxy a' a b' b m (Maybe r) -> Proxy a' a b' b (M.MaybeT m) r
maybeP p = do
    x <- unsafeHoist lift p
    lift $ M.MaybeT (return x)
{-# INLINABLE maybeP #-}

-- | Run 'M.MaybeT' in the base monad
runMaybeP
    :: (Monad m)
    => Proxy a' a b' b (M.MaybeT m) r -> Proxy a' a b' b m (Maybe r)
runMaybeP = go
  where
    go p = case p of
        Request a' fa  -> Request a' (\a  -> go (fa  a ))
        Respond b  fb' -> Respond b  (\b' -> go (fb' b'))
        Pure    r      -> Pure (Just r)
        M          m   -> M (do
            x <- M.runMaybeT m
            return (case x of
                Nothing -> Pure Nothing
                Just p' -> go p' ) )
{-# INLINABLE runMaybeP #-}

-- | Pull 'M.MaybeT' outside of Proxy.  This is a monad morphism.
distMaybeP
    :: (Monad m)
    => Proxy a' a b' b (M.MaybeT m) r
    -> M.MaybeT (Proxy a' a b' b m) r
distMaybeP p = M.MaybeT (runMaybeP p)
{-# INLINABLE distMaybeP #-}

-- | Wrap the base monad in 'M.MaybeT'
maybeF
    :: (Monad m, Functor f)
    => F.FreeT f m (Maybe r) -> F.FreeT f (M.MaybeT m) r
maybeF m = do
    x <- hoistF lift m
    lift $ M.MaybeT (return x)
{-# INLINABLE maybeF #-}

-- | Run 'M.MaybeT' in the base monad
runMaybeF
    :: (Monad m, Functor f)
    => F.FreeT f (M.MaybeT m) r -> F.FreeT f m (Maybe r)
runMaybeF = go
  where
    go m = F.FreeT (do
        x <- M.runMaybeT (F.runFreeT m)
        return (case x of
            Nothing         -> F.Pure Nothing
            Just (F.Pure r) -> F.Pure (Just r)
            Just (F.Free f) -> F.Free (fmap go f) ) )
{-# INLINABLE runMaybeF #-}

-- | Pull 'E.ErrorT' outside of 'F.FreeT'.  This is a monad morphism.
distMaybeF
    :: (Monad m, Functor f)
    => F.FreeT f (M.MaybeT m) r -> M.MaybeT (F.FreeT f m) r
distMaybeF m = M.MaybeT (runMaybeF m)
{-# INLINABLE distMaybeF #-}

-- | Wrap the base monad in 'R.ReaderT'
readerP
    :: (Monad m)
    => (i -> Proxy a' a b' b m r) -> Proxy a' a b' b (R.ReaderT i m) r
readerP k = do
    i <- lift R.ask
    unsafeHoist lift (k i)
{-# INLINABLE readerP #-}

-- | Run 'R.ReaderT' in the base monad
runReaderP
    :: (Monad m)
    => i -> Proxy a' a b' b (R.ReaderT i m) r -> Proxy a' a b' b m r
runReaderP i = go
  where
    go p = case p of
        Request a' fa  -> Request a' (\a  -> go (fa  a ))
        Respond b  fb' -> Respond b  (\b' -> go (fb' b'))
        Pure    r      -> Pure r
        M          m   -> M (do
            p' <- R.runReaderT m i
            return (go p') )
{-# INLINABLE runReaderP #-}

-- | Pull 'R.ReaderT' outside of Proxy.  This is a monad morphism.
distReaderP
    :: (Monad m)
    => Proxy a' a b' b (R.ReaderT i m) r
    -> R.ReaderT i (Proxy a' a b' b m) r
distReaderP p = R.ReaderT (flip runReaderP p)
{-# INLINABLE distReaderP #-}

-- | Wrap the base monad in 'R.ReaderT'
readerF
    :: (Monad m, Functor f)
    => (i -> F.FreeT f m r) -> F.FreeT f (R.ReaderT i m) r
readerF k = do
    i <- lift R.ask
    hoistF lift (k i)
{-# INLINABLE readerF #-}

-- | Run 'R.ReaderT' in the base monad
runReaderF
    :: (Monad m, Functor f)
    => i -> F.FreeT f (R.ReaderT i m) r -> F.FreeT f m r
runReaderF i = go
  where
    go m = F.FreeT (do
        x <- R.runReaderT (F.runFreeT m) i
        return (case x of
            F.Pure r -> F.Pure r
            F.Free f -> F.Free (fmap go f) ) )
{-# INLINABLE runReaderF #-}

-- | Pull 'R.ReaderT' outside of 'F.FreeT'.  This is a monad morphism.
distReaderF
    :: (Monad m, Functor f)
    => F.FreeT f (R.ReaderT i m) r -> R.ReaderT i (F.FreeT f m) r
distReaderF m = R.ReaderT (flip runReaderF m)
{-# INLINABLE distReaderF #-}

-- | Wrap the base monad in 'S.StateT'
stateP
    :: (Monad m)
    => (s -> Proxy a' a b' b m (r, s)) -> Proxy a' a b' b (S.StateT s m) r
stateP k = do
    s <- lift S.get
    (r, s') <- unsafeHoist lift (k s)
    lift (S.put s')
    return r
{-# INLINABLE stateP #-}

-- | Run 'S.StateT' in the base monad
runStateP
    :: (Monad m)
    => s -> Proxy a' a b' b (S.StateT s m) r -> Proxy a' a b' b m (r, s)
runStateP = go
  where
    go s p = case p of
        Request a' fa  -> Request a' (\a  -> go s (fa  a ))
        Respond b  fb' -> Respond b  (\b' -> go s (fb' b'))
        Pure    r      -> Pure (r, s)
        M          m   -> M (do
            (p', s') <- S.runStateT m s
            return (go s' p') )
{-# INLINABLE runStateP #-}

-- | Evaluate 'S.StateT' in the base monad
evalStateP
    :: (Monad m) => s -> Proxy a' a b' b (S.StateT s m) r -> Proxy a' a b' b m r
evalStateP s = fmap fst . runStateP s
{-# INLINABLE evalStateP #-}

-- | Execute 'S.StateT' in the base monad
execStateP
    :: (Monad m) => s -> Proxy a' a b' b (S.StateT s m) r -> Proxy a' a b' b m s
execStateP s = fmap snd . runStateP s
{-# INLINABLE execStateP #-}

-- | Pull 'S.StateT' outside of Proxy.  This is a monad morphism.
distStateP
    :: (Monad m)
    => Proxy a' a b' b (S.StateT s m) r
    -> S.StateT s (Proxy a' a b' b m) r
distStateP p = S.StateT (flip runStateP p)
{-# INLINABLE distStateP #-}

-- | Wrap the base monad in 'S.StateT'
stateF
    :: (Monad m, Functor f)
    => (s -> F.FreeT f m (r, s)) -> F.FreeT f (S.StateT s m) r
stateF k = do
    s <- lift S.get
    (r, s') <- hoistF lift (k s)
    lift (S.put s')
    return r
{-# INLINABLE stateF #-}

-- | Run 'S.StateT' in the base monad
runStateF
    :: (Monad m, Functor f)
    => s -> F.FreeT f (S.StateT s m) r -> F.FreeT f m (r, s)
runStateF = go
  where
    go s m = F.FreeT (do
        (x, s') <- S.runStateT (F.runFreeT m) s
        return (case x of
            F.Pure r -> F.Pure (r, s')
            F.Free f -> F.Free (fmap (go s') f) ) )
{-# INLINABLE runStateF #-}

-- | Evaluate 'S.StateT' in the base monad
evalStateF
    :: (Monad m, Functor f) => s -> F.FreeT f (S.StateT s m) r -> F.FreeT f m r
evalStateF s = fmap fst . runStateF s
{-# INLINABLE evalStateF #-}

-- | Execute 'S.StateT' in the base monad
execStateF
    :: (Monad m, Functor f) => s -> F.FreeT f (S.StateT s m) r -> F.FreeT f m s
execStateF s = fmap snd . runStateF s
{-# INLINABLE execStateF #-}

-- | Pull 'S.StateT' outside of 'F.FreeT'.  This is a monad morphism.
distStateF
    :: (Monad m, Functor f)
    => F.FreeT f (S.StateT s m) r -> S.StateT s (F.FreeT f m) r
distStateF m = S.StateT (flip runStateF m)
{-# INLINABLE distStateF #-}

{- $writert
    Note that 'runWriterP' and 'execWriterP' will keep the accumulator in
    weak-head-normal form so that folds run in constant space when possible.

    This means that until @transformers@ adds a truly strict 'W.WriterT', you
    should consider unwrapping 'W.WriterT' first using 'runWriterP' or
    'execWriterP' before 'Pipes.run'ning your 'Proxy'.  You will get better
    performance this way and eliminate space leaks if your accumulator doesn't
    have any lazy fields.
-}

-- | Wrap the base monad in 'W.WriterT'
writerP
    :: (Monad m, Monoid w)
    => Proxy a' a b' b m (r, w) -> Proxy a' a b' b (W.WriterT w m) r
writerP p = do
    (r, w) <- unsafeHoist lift p
    lift $ W.tell w
    return r
{-# INLINABLE writerP #-}

-- | Run 'W.WriterT' in the base monad
runWriterP
    :: (Monad m, Monoid w)
    => Proxy a' a b' b (W.WriterT w m) r -> Proxy a' a b' b m (r, w)
runWriterP = go mempty
  where
    go w p = case p of
        Request a' fa  -> Request a' (\a  -> go w (fa  a ))
        Respond b  fb' -> Respond b  (\b' -> go w (fb' b'))
        Pure  r      -> Pure (r, w)
        M        m   -> M (do
            (p', w') <- W.runWriterT m
            let wt = mappend w w'
            wt `seq` return (go wt p') )
{-# INLINABLE runWriterP #-}

-- | Execute 'W.WriterT' in the base monad
execWriterP
    :: (Monad m, Monoid w)
    => Proxy a' a b' b (W.WriterT w m) r -> Proxy a' a b' b m w
execWriterP = fmap snd . runWriterP
{-# INLINABLE execWriterP #-}

-- | Pull 'W.WriterT' outside of Proxy.  This is a monad morphism.
distWriterP
    :: (Monad m, Monoid w)
    => Proxy a' a b' b (W.WriterT w m) r
    -> W.WriterT w (Proxy a' a b' b m) r
distWriterP p = W.WriterT (runWriterP p)
{-# INLINABLE distWriterP #-}

-- | Wrap the base monad in 'W.WriterT'
writerF
    :: (Monad m, Functor f, Monoid w)
    => F.FreeT f m (r, w) -> F.FreeT f (W.WriterT w m) r
writerF m = do
    (r, w) <- hoistF lift m
    lift $ W.tell w
    return r
{-# INLINABLE writerF #-}

-- | Run 'W.WriterT' in the base monad
runWriterF
    :: (Monad m, Functor f, Monoid w)
    => F.FreeT f (W.WriterT w m) r -> F.FreeT f m (r, w)
runWriterF = go mempty
  where
    go w m = F.FreeT (do
        (x, w') <- W.runWriterT (F.runFreeT m)
        let wt = mappend w w'
        wt `seq` return (case x of
            F.Pure r -> F.Pure (r, wt)
            F.Free f -> F.Free (fmap (go wt) f) ) )
{-# INLINABLE runWriterF #-}

-- | Execute 'W.WriterT' in the base monad
execWriterF
    :: (Monad m, Functor f, Monoid w)
    => F.FreeT f (W.WriterT w m) r -> F.FreeT f m w
execWriterF = fmap snd . runWriterF
{-# INLINABLE execWriterF #-}

-- | Pull 'W.WriterT' outside of 'F.FreeT'.  This is a monad morphism.
distWriterF
    :: (Monad m, Functor f, Monoid w)
    => F.FreeT f (W.WriterT w m) r -> W.WriterT w (F.FreeT f m) r
distWriterF m = W.WriterT (runWriterF m)
{-# INLINABLE distWriterF #-}

-- | Wrap the base monad in 'RWS.RWST'
rwsP
    :: (Monad m, Monoid w)
    => (i -> s -> Proxy a' a b' b m (r, s, w))
    -> Proxy a' a b' b (RWS.RWST i w s m) r
rwsP k = do
    i <- lift RWS.ask
    s <- lift RWS.get
    (r, s', w) <- unsafeHoist lift (k i s)
    lift $ do
        RWS.put s'
        RWS.tell w
    return r
{-# INLINABLE rwsP #-}

-- | Run 'RWST' in the base monad
runRWSP :: (Monad m, Monoid w)
        => i
        -> s
        -> Proxy a' a b' b (RWS.RWST i w s m) r
        -> Proxy a' a b' b m (r, s, w)
runRWSP i = go mempty
  where
    go w s p = case p of
        Request a' fa  -> Request a' (\a  -> go w s (fa  a ))
        Respond b  fb' -> Respond b  (\b' -> go w s (fb' b'))
        Pure    r      -> Pure (r, s, w)
        M          m   -> M (do
            (p', s', w') <- RWS.runRWST m i s
            let wt = mappend w w'
            wt `seq` return (go w' s' p') )
{-# INLINABLE runRWSP #-}

-- | Evaluate 'RWST' in the base monad
evalRWSP :: (Monad m, Monoid w)
         => i
         -> s
         -> Proxy a' a b' b (RWS.RWST i w s m) r
         -> Proxy a' a b' b m (r, w)
evalRWSP i s = fmap go . runRWSP i s
    where go (r, _, w) = (r, w)
{-# INLINABLE evalRWSP #-}

-- | Execute 'RWST' in the base monad
execRWSP :: (Monad m, Monoid w)
         => i
         -> s
         -> Proxy a' a b' b (RWS.RWST i w s m) r
         -> Proxy a' a b' b m (s, w)
execRWSP i s = fmap go . runRWSP i s
    where go (_, s', w) = (s', w)
{-# INLINABLE execRWSP #-}

-- | Pull 'RWST' outside of Proxy.  This is a monad morphism.
distRWSP
    :: (Monad m, Monoid w)
    => Proxy a' a b' b (RWS.RWST i w s m) r
    -> RWS.RWST i w s (Proxy a' a b' b m) r
distRWSP p = RWS.RWST (\i s -> runRWSP i s p)
{-# INLINABLE distRWSP #-}

