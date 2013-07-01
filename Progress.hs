-- Monad transformer for progress tracking.
module Progress(Progress(..), ProgressT(..), progress, showProgress) where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans.Class
import Text.Printf

data Progress d a = Progress d (Progress d a) | ProgressLift a

instance Functor (Progress d) where
    f `fmap` Progress p px = Progress p $ fmap f px
    f `fmap` ProgressLift x = ProgressLift $ f x

showProgress :: Progress Float a -> IO a
showProgress (Progress p px) = printf "\r%.0f%%" (100 * p) >> showProgress px
showProgress (ProgressLift x) = putStrLn "\rDone.       " >> return x

newtype ProgressT d m a = ProgressT { runProgressT :: m (Progress d a) }

instance (Monad m) => Monad (ProgressT d m) where
    return x = ProgressT $ return $ ProgressLift x
    ProgressT mpx >>= f = ProgressT $ do
        px <- mpx
        bind px f
        where bind (Progress p py) f = liftM (Progress p) $ bind py f
              bind (ProgressLift y) f = runProgressT $ f y

instance (Monad m) => Functor (ProgressT d m) where
    fmap f x = liftM f x

instance MonadTrans (ProgressT d) where
    lift m = ProgressT $ liftM ProgressLift m

instance (Monad m) => Applicative (ProgressT d m) where
    pure = return
    (<*>) = ap

progress :: (Monad m) => d -> ProgressT d m ()
progress p = ProgressT $ return $ Progress p $ ProgressLift ()
