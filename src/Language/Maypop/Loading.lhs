In this module, we'll define how modules are loaded from disk
and into the interpreter.

> {-# LANGUAGE FlexibleContexts #-}
> module Language.Maypop.Loading where
> import Language.Maypop.Syntax
> import Language.Maypop.Modules
> import Language.Maypop.Checking
> import Control.Monad.Except
> import Control.Monad.Reader
> import Control.Monad.State
> import Control.Exception hiding (TypeError)
> import Data.Bool
> import Data.Bifunctor
> import Data.Either
> import Data.List
> import qualified Data.Map as Map

Now that we know what constitutes a module, we should try get a mechanism
working that will dynamically import and explore various modules. For instance,
it may start the file the user loads, find its dependencies, and try to load those;
the dependencies may themselves have dependencies, and so on.

We will require some kind of way to load modules from disk. The first thought here is `IO`, but because it is so contagious, we'd rather
avoid writing straight up `IO` code everywhere. Instead, we'll define a type class for
a "monad that can load modules", which will have two steps: loading a module's header (which
includes includes the module's name and its imports) and loading its definitions. Separating
this functionality into an interface will also allow us to mock module loading.
Here is the type class:

{{< todo >}}This is a little awkward. Maybe we need to think a bit more about what <code>MonadModule</code> should provide? {{< /todo >}}

> class Monad m => MonadModule m where
>     moduleHeader :: String -> m (Either LoadingError (String, ModuleHeader))
>     moduleContent :: String -> GlobalScope -> m (Either LoadingError Module)

In principle, we'll have module files on disk. But where? There's probably a standard directory
for the "base" package, and then there's the source folder of the user-created Maypop project.
Thus, each symbol, like `Data.Nat`, may refer to different physical locations. Let's create a type
class for something that can compute these physical locations:

> class Monad m => MonadModulePath m where
>     modulePaths :: Symbol -> m [String]

Given that, we can write a function to explore modules starting at a particular one
(for instance, the one that the user selected). This can go wrong, for several reasons:

* We may not find a file for a particular module name at all.
* We may find too many module files (for instance, if the user tries
to re-define `Data.Nat`). We have no way of picking a "better" module. 
* We may find a module in the path, but whose header claims it has a different
name! This is also an error.
* We may run into a dependency cycle. We will not allow these in Maypop programs.

> data LoadingError
>     = NoSuchFile
>     | DuplicateModules
>     | MismatchedName
>     | Cycle
>     | ImportError ImportError
>     | TypeError TypeError

Let's write a few functions to detect these errors.

> verifyHeader :: MonadError LoadingError m => Symbol -> ModuleHeader -> m ()
> verifyHeader s mh = if s == mhName mh then return () else throwError MismatchedName
>
> verifyLoaded :: MonadError LoadingError m => [(String, ModuleHeader)] -> m (String,ModuleHeader)
> verifyLoaded [] = throwError NoSuchFile
> verifyLoaded [x] = return x
> verifyLoaded _ = throwError DuplicateModules
>
> verifyCycle :: (MonadError LoadingError m, MonadReader [Symbol] m) => Symbol -> m ()
> verifyCycle s = asks (s `elem`) >>= bool (return ()) (throwError Cycle)
>
> verifyUniquePaths :: MonadError LoadingError m => [(Symbol, ModuleImport)] -> m ()
> verifyUniquePaths _ = return () -- TODO

With that in hand, let's write our module loading code!

> loadModule
>     :: (MonadError LoadingError m, MonadModule m, MonadModulePath m, MonadReader [Symbol] m)
>     => Symbol -> m Module
> loadModule s = do
>     verifyCycle s
>     paths <- modulePaths s
>     (path, mh) <- rights <$> mapM moduleHeader paths >>= verifyLoaded
>     verifyHeader s mh
>     verifyUniquePaths (mhImports mh)
>     let (ss, is) = unzip (mhImports mh)
>     ms <- mapM (local (s:) . loadModule) ss
>     gss <- liftEither $ first ImportError $ zipWithM moduleScope is ms
>     gs <- liftEither $ first ImportError $ foldM mergeScopes emptyScope gss
>     moduleContent path gs >>= liftEither
