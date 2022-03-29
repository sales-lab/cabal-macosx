{- | Inclusion of bundle-local copies of libraries in application bundles.

OS X application bundles can include local copies of libraries and
frameworks (ie dependencies of the executable) which aids distribution
and eases installation.  Xcode and the traditional OS X development
toolchain support this fairly transparently; this module is an attempt
to provide similar functionality in the cabal-macosx package.

The basic approach is as follows:

  1. Discover the libraries an object file (executable, other binary, or
     library) references using @otool -L /path/@

  2. Copy those libraries into the application bundle, at the right
     place, ie @\@executable_path\/..\/Frameworks\/@ where
     @\@executable_path@ represents the path to the exeutable in the
     bundle.

  3. Modify the object file so it refers to the local copy, using
     @install_name_tool -change /oldLibPath/ /newLibPath/ /path/@ where
     @/newlibPath/@ points to @\@executable_path\/..\/Frameworks@ as
     described above (@\@executable_path@ is a special symbol recognised
     by the loader).

Complications:

  * There's some stuff we don't want to include because we can
  expect it to be present everywhere, eg the Cocoa framework; see
  /Exclusions/, below.

  * Libraries can themselves depend on other libraries; thus, we
  need to copy them in recursively.

  * Because of these transitive dependencies, dependencies can
  arise on multiple copies of the same library, in different
  locations (eg @\/usr\/lib\/libfoo@ and @\/opt\/local\/lib\/libfoo@).
  Thus, we preserve that path info, and (for example) copy
  @\/usr\/lib\/libFoo@ to
  @\@executable_path\/..\/Frameworks\/usr\/lib\/@.

The approach followed is to build a dependency graph, seeded with the
executable and any other binaries being included in the bundle, using
@otool@; then to walk that graph, copying in the libraries, and
calling @install_name_tool@ to update the dependencies of entities in
the bundle.  Going via a dependency graph is a bit unnecessary - we
could just recursively @otool@/@install_name_tool@, but its helpful if
we need to debug, etc., and a nice clear abstraction.

/Exclusions/: as described above, a lot of truly common stuff would
get copied in, so we provide a mechanism to exclude libraries from
this process: 'buildDependencyGraph' can be passed a list of strings,
and a library whose path includes any of those strings is excluded.
If an empty list is passed, then nothing is excluded (which is almost
certainly not what you want).

-}

module Distribution.MacOSX.Dependencies (
  includeDependencies,
  appDependencyGraph
) where

import Control.Exception
import Control.Monad
import Crypto.Hash
import Crypto.Hash.IO
import qualified Data.ByteString.Lazy as B
import Data.IORef
import Data.List
import qualified Data.Map.Strict as M
import Data.Maybe
import System.Directory
import System.Exit
import System.FilePath
import System.IO.Error
import System.Process
import Text.ParserCombinators.Parsec

import Distribution.MacOSX.Common
import Distribution.MacOSX.DG


-- | Deduplicated dependency, referencing a file and possibly an already
-- exising copy to link to.
data DDeps = DDeps FDeps (Maybe FilePath)


-- | Include any library dependencies required in the app.
includeDependencies ::
  FilePath -- ^ Path to application bundle root.
  -> MacApp -> IO ()
includeDependencies appPath app =
  do dg <- appDependencyGraph appPath app
     let fDeps = dgFDeps dg
     dDeps <- dedupDependencies fDeps
     mapM_ (copyInDependency appPath app) dDeps
     mapM_ (updateDependencies appPath app) fDeps

-- | Compute application's library dependency graph.
appDependencyGraph ::
  FilePath -- ^ Path to application bundle root.
  -> MacApp -> IO DG
appDependencyGraph appPath app =
  case (appDeps app) of
    ChaseWithDefaults -> appDependencyGraph appPath app {
                           appDeps = ChaseWith defaultExclusions
                         }
    ChaseWith xs -> do putStrLn "Building dependency graph"
                       buildDependencyGraph appPath app dgInitial roots [] xs
    DoNotChase -> return dgInitial
  where roots = appName app : otherBins app
        dgInitial = dgEmpty `dgAddPaths` roots

-- | Recursive dependency-graph builder.
buildDependencyGraph ::
  FilePath -- ^ Path to application bundle root.
  -> MacApp
  -> DG -- ^ Dependency graph to be extended.
  -> [FilePath] -- ^ Queue of paths to object files to be examined for
                -- dependencies.
  -> [FilePath] -- ^ List of paths of object files which have already
                -- been dealt with.
  -> Exclusions -- ^ List of exclusions for dependency-chasing.
  -> IO DG
buildDependencyGraph _ _ dg [] _ _ = return dg
buildDependencyGraph appPath app dg (x:xs) done excls =
  do (dg', tgts) <- addFilesDependencies appPath app dg x excls
     let done' = (x:done)
         xs'   = addToQueue xs done' tgts
     buildDependencyGraph appPath app dg' xs' done' excls
  where addToQueue :: [FilePath] -> [FilePath] -> [FilePath] -> [FilePath]
        addToQueue q done' = foldl (addOneToQueue (q ++ done')) q
        addOneToQueue :: [FilePath] -> [FilePath] -> FilePath -> [FilePath]
        addOneToQueue done' q n = if n `elem` done' then q else q ++ [n]

-- | Add an object file's dependencies to a dependency graph,
-- returning that new graph and a list of the discovered dependencies.
addFilesDependencies ::
  FilePath -- ^ Path to application bundle root.
  -> MacApp
  -> DG -- ^ Dependency graph to be extended.
  -> FilePath -- ^ Path to object file to be examined for dependencies.
  -> Exclusions -- ^ List of exclusions for dependency chasing.
  -> IO (DG, [FilePath])
addFilesDependencies appPath app dg p excls =
  do (FDeps _ tgts) <- getFDeps appPath app p excls
     let dg' = dgAddFDeps dg (FDeps p tgts)
     return (dg', tgts)

-- | Compute the library dependencies for some file, removing any
-- exclusions.
getFDeps ::
  FilePath -- ^ Path to application bundle root.
  -> MacApp
  -> FilePath -- ^ Path to object file to be examined for dependencies.
  -> Exclusions -- ^ List of exclusions for dependency chasing.
  -> IO FDeps
getFDeps appPath app path exclusions =
  do putStrLn $ "path: " ++ path
     contents <- readProcess oTool ["-L", absPath] ""
     putStrLn $ "contents: " ++ contents
     case parse parseFileDeps "" contents of
       Left err -> error $ show err
       Right fDeps -> return $ exclude exclusions fDeps
  where absPath = if path == appName app then
                    appPath </> pathInApp app (appName app)
                  else path
        parseFileDeps :: Parser FDeps
        parseFileDeps = do f <- manyTill (noneOf ":") (char ':')
                           _ <- char '\n'

                           deps <- parseDepOrName `sepEndBy` char '\n'
                           eof
                           return $ FDeps f $ filter (f /=) $ catMaybes deps
        parseDepOrName :: Parser (Maybe FilePath)
        parseDepOrName = do c <- oneOf "\t/"
                            case c of
                              '\t' -> -- A dependency.
                                      do dep <- parseDepOrIgnoreAt
                                         return $ dep
                              '/' -> -- Same filename, alternative arch
                                     do _ <- manyTill (noneOf ":") (char ':')
                                        return Nothing
                              _ -> error "Can't happen"
        parseDepOrIgnoreAt :: Parser (Maybe FilePath)
        parseDepOrIgnoreAt = do c <- lookAhead (oneOf "/@")
                                case c of
                                  '/' -> -- A dependency.
                                         do dep <- parseDep
                                            return $ Just $ dep
                                  '@' -> -- ignore entries that start with @
                                         do _ <- manyTill (noneOf ")") (char ')')
                                            return Nothing
                                  _ -> error "Can't happen"
        parseDep :: Parser FilePath
        parseDep = do dep <- manyTill (noneOf " ") (char ' ')
                      _ <- char '('
                      _ <- manyTill (noneOf ")") (char ')')
                      return dep

-- | Apply an exclusion list to an 'FDeps' value; any dependencies
-- which contain any of the exclusions as substrings are excluded.
exclude :: Exclusions -> FDeps -> FDeps
exclude excls (FDeps p ds) = FDeps p $ filter checkExclude ds
  where checkExclude :: FilePath -> Bool
        checkExclude f = not $ any (`isInfixOf` f) excls

-- | Deduplicate dependencies, transforming some files into links.
dedupDependencies :: [FDeps] -> IO [DDeps]
dedupDependencies deps = run
  where
    run = do
      digests <- newIORef mempty
      mapM (loop digests) deps

    loop digests fd@(FDeps src _) = DDeps fd <$>
      handleJust (guard . isDoesNotExistError)
                 (const $ return Nothing)
                 (computeDigest src >>= dedupWithDigest digests src)

-- | Compute the digest of a file content.
computeDigest :: FilePath -> IO (Digest SHA256)
computeDigest filename = do
  putStrLn $ "Computing hash of " ++ filename
  bytes <- B.readFile filename
  ctx <- hashMutableInit
  mapM_ (hashMutableUpdate ctx) (B.toChunks bytes)
  hashMutableFinalize ctx

-- | Store the file digest in the provided map, returning the path of another
-- file with the same content if it can be found.
dedupWithDigest :: IORef (M.Map (Digest SHA256) FilePath)
                -> FilePath
                -> Digest SHA256
                -> IO (Maybe FilePath)
dedupWithDigest digests filename digest = do
  digests' <- readIORef digests
  let other = M.lookup digest digests'
  when (isNothing other) $
    writeIORef digests $! M.insert digest filename digests'
  return other

-- | Copy some object file's library dependencies into the application
-- bundle.
copyInDependency ::
  FilePath -- ^ Path to application bundle root.
  -> MacApp
  -> DDeps -- ^ Dependencies to copy in.
  -> IO ()
copyInDependency appPath app (DDeps (FDeps src _) linkTo) =
  Control.Monad.unless (src == appName app) $
    case linkTo of
      Nothing -> do
        putStrLn $ "Copying " ++ src ++ " to " ++ tgt
        createDirectoryIfMissing True $ takeDirectory tgt
        copyFile src tgt
      Just linkRaw -> do
        let linkRel = relativePath tgt (appPath </> pathInApp app linkRaw)
        putStrLn $ "Linking " ++ tgt ++ " to " ++ linkRel
        createDirectoryIfMissing True $ takeDirectory tgt
        removePathForcibly tgt
        createFileLink linkRel tgt
  where tgt = appPath </> pathInApp app src

-- | Transform a path into a relative form, with respect to a second path.
relativePath :: FilePath -> FilePath -> FilePath
relativePath path ref =
  let (pathS, refS) = dropCommonPrefix (splitPath path) (splitPath ref)
  in joinPath (replicate (length pathS - 1) ".." ++ refS)

dropCommonPrefix :: Eq a => [a] -> [a] -> ([a], [a])
dropCommonPrefix xs ys =
  if null xs || null ys || head xs /= head ys
     then (xs, ys)
     else dropCommonPrefix (tail xs) (tail ys)

-- | Update some object file's library dependencies to point to
-- bundled copies of libraries.
updateDependencies ::
  FilePath -- ^ Path to application bundle root.
  -> MacApp
  -> FDeps -- ^ Dependencies to update.
  -> IO ()
updateDependencies appPath app (FDeps src tgts) =
  mapM_ (updateDependency appPath app src) tgts

-- | Update some object file's dependency on some particular library,
-- to point to the bundled copy of that library.
updateDependency ::
  FilePath -- ^ Path to application bundle root.
  -> MacApp
  -> FilePath -- ^ Path to object file to update.
  -> FilePath -- ^ Path to library which was copied in (path before copy).
  -> IO ()
updateDependency appPath app src tgt =
  do putStrLn $ "Updating " ++ newLib ++ "'s dependency on " ++ tgt ++
                   " to " ++ tgt'
     -- Ensure we have write permissions while editing the library. Notably,
     -- Homebrew removes write permissions from installed files.
     perm <- getPermissions newLib
     setPermissions newLib perm { writable = True }
     let cmd = iTool ++ " -change " ++ show tgt ++ " " ++ show tgt' ++
                   " " ++ show newLib
     exitCode <- system cmd
     setPermissions newLib perm
     when (exitCode /= ExitSuccess) $
       error $ "Failed to update library dependencies on " ++ show newLib ++
        " with command: " ++ cmd
     return ()
  where tgt' = "@executable_path/../Frameworks/" </> makeRelative "/" tgt
        newLib = appPath </> pathInApp app src

-- | Path to @otool@ tool.
oTool :: FilePath
oTool = "/usr/bin/otool"

-- | Path to @install_name_tool@ tool.
iTool :: FilePath
iTool = "/usr/bin/install_name_tool"