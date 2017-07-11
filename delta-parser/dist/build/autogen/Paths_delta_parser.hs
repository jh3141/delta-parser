module Paths_delta_parser (
    version,
    getBinDir, getLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
catchIO = Exception.catch

version :: Version
version = Version [0,1] []
bindir, libdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "C:\\Users\\admin\\AppData\\Roaming\\cabal\\bin"
libdir     = "C:\\Users\\admin\\AppData\\Roaming\\cabal\\x86_64-windows-ghc-7.10.2\\delta-parser-0.1-3Wl3Ji4jG7N7iXL1d1nn6Y"
datadir    = "C:\\Users\\admin\\AppData\\Roaming\\cabal\\x86_64-windows-ghc-7.10.2\\delta-parser-0.1"
libexecdir = "C:\\Users\\admin\\AppData\\Roaming\\cabal\\delta-parser-0.1-3Wl3Ji4jG7N7iXL1d1nn6Y"
sysconfdir = "C:\\Users\\admin\\AppData\\Roaming\\cabal\\etc"

getBinDir, getLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "delta_parser_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "delta_parser_libdir") (\_ -> return libdir)
getDataDir = catchIO (getEnv "delta_parser_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "delta_parser_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "delta_parser_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "\\" ++ name)
