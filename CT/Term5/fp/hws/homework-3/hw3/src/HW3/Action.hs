{-# LANGUAGE ScopedTypeVariables #-}

module HW3.Action
  ( HiPermission(..)
  , PermissionException(..)
  , HIO(..) ) where

import Control.Exception (Exception, catch, throwIO)
import qualified Data.ByteString as BS
import qualified Data.Sequence as SEQ
import Data.Set (Set)
import qualified Data.Text as T
import qualified Data.Text.Encoding as ENC
import qualified Data.Time as UTC
import HW3.Base
import System.Directory (createDirectory, doesDirectoryExist, getCurrentDirectory, listDirectory,
                         setCurrentDirectory)
import qualified System.Random as R

data HiPermission = AllowRead
                  | AllowWrite
                  | AllowTime
                  deriving (Show, Eq, Ord, Enum, Bounded)

data PermissionException = PermissionRequired HiPermission
  deriving (Show)

instance Exception PermissionException

newtype HIO a = HIO { runHIO :: Set HiPermission -> IO a }

instance Functor HIO where
  fmap f (HIO hio) = HIO $ \perm -> fmap f (hio perm)

instance Applicative HIO where
  pure v = HIO $ \_ -> pure v
  fM <*> aM = HIO $ \perm -> do
    f <- runHIO fM perm
    a <- runHIO aM perm
    pure $ f a

instance Monad HIO where
  m >>= f = HIO $ \perm -> do
    v <- runHIO m perm
    runHIO (f v) perm

-- | Checks giving permission is presented, perform action if allowed
checkingPerm :: [HiPermission] -> IO HiValue -> HIO HiValue
checkingPerm neededPerms io = HIO $ \perms ->
  let present = map (\p -> (p, p `elem` perms)) neededPerms
  in if all snd present
  then catch io $ \(_ :: IOError) -> pure HiValueNull
  else throwIO $ PermissionRequired $ fst $ head $ filter (not . snd) present

instance HiMonad HIO where
  runAction HiActionCwd = checkingPerm [AllowRead] $
    HiValueString . T.pack <$> getCurrentDirectory
  runAction (HiActionChDir dir) = checkingPerm [AllowRead] $
    HiValueNull <$ setCurrentDirectory dir
  runAction (HiActionRead file) = checkingPerm [AllowRead] $
    do
      isDir <- doesDirectoryExist file
      if isDir
      then do
        list <- listDirectory file
        pure $ HiValueList $ SEQ.fromList $ map (HiValueString . T.pack) list
      else do
        content <- BS.readFile file
        case ENC.decodeUtf8' content of
          Left _  -> pure $ HiValueBytes content
          Right s -> pure $ HiValueString s
  runAction (HiActionWrite file content) = checkingPerm [AllowWrite] $
    HiValueNull <$ BS.writeFile file content
  runAction (HiActionMkDir path) = checkingPerm [AllowWrite] $
    HiValueNull <$ createDirectory path
  runAction HiActionNow = checkingPerm [AllowTime] $
    HiValueTime <$> UTC.getCurrentTime
  runAction (HiActionRand from to) = checkingPerm [] $
    do
      r <- R.getStdRandom $ R.uniformR (from, to)
      pure $ HiValueNumber $ toRational r
  runAction (HiActionEcho s) = checkingPerm [AllowWrite] $
    do
      putStrLn $ T.unpack s
      pure HiValueNull


