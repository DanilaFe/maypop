We've defined a module loading monad type class elsewhere. In this
module, we actually pay the cost of implementing this monad and its
friends.

> {-# LANGUAGE GeneralizedNewtypeDeriving #-}
> {-# LANGUAGE FlexibleInstances #-}
> {-# LANGUAGE ScopedTypeVariables #-}
> {-# LANGUAGE MultiParamTypeClasses #-}
> {-# LANGUAGE UndecidableInstances #-}
> module Language.Maypop.LoadingImpl where
> import Language.Maypop.Loading
> import Language.Maypop.Modules
> import Language.Maypop.Parser
> import Control.Monad.Reader
> import Control.Monad.Except
> import Control.Exception
> import Data.List
> import Data.Bifunctor
> import qualified Data.Map as Map

The easiest thing to start with is the `MonadModulePath` type class.
We really need something that's like a `MonadReader [String]`, where
`[String]` represents the list of all possible search paths. Unfortunately
it seems to me that nesting multiple `MonadReader` instances doesn't quite work.
Instead, we'll have to define a similar monad transformer, that is specifically
_not_ a `MonadReader`. Let's call it `PathT`:

> newtype PathT m a = MkPathT { unPathT :: ReaderT [String] m a }
>     deriving (Functor, Applicative, Monad, MonadTrans)

Running this monad transformer is practically idential to running
a `ReaderT`, except that the environment can only have one type: `[String]`.

> runPathT :: PathT m a -> [String] -> m a
> runPathT = runReaderT . unPathT

Of course, we want `PathT` to be an instance of `MonadModulePath`. For now,
we totally ingore Windows and use the Linux file separator. We also use  the `.mp` extension
for Maypop source files.

> instance Monad m => MonadModulePath (PathT m) where
>     modulePaths s = MkPathT $ asks $ map ((++symbolFilePath s) . (++"/"))

We want to acces the methods of `MonadModulePath` even if the `PathT` is not
the outermost monad in our stack. We thus define a way for the type class to
propagate through `ReaderT` and `ExceptT`, which are the only two other
transformers we are using for loading.

> instance MonadModulePath m => MonadModulePath (ReaderT r m) where
>     modulePaths s = lift $ modulePaths s

> instance MonadModulePath m => MonadModulePath (ExceptT e m) where
>     modulePaths s = lift $ modulePaths s

With that out of the way, it's time to move on to `MonadModule`. As we mentioned
in the `Loading` module, the most obvious way of loading files is `IO`. Let's
define an instance of `MonadModule` for `IO`, that naively looks up and parses a file.
Since we don't keep any kind of context between calls to `moduleHeader` and `moduleContent`,
we'll simply parse the file anew each time.

> parseH :: String -> String -> Either LoadingError (ModuleHeader, String)
> parseH m s = first (ParseError) $ parseHeader m s
>
> parseH' :: String -> String -> Either LoadingError ModuleHeader
> parseH' m s = fst <$> parseH m s
>
> parseD :: String -> String -> Either LoadingError [(String, ParseDef)]
> parseD m s = first (ParseError) $ parseDefs m s

> instance MonadModule IO where
>     moduleHeader s = handle (\(e :: IOException) -> return $ Left NoSuchFile)
>         $ fmap ((,) s) <$> parseH' s <$> readFile s
>     moduleContent s = handle (\(e :: IOException) -> return $ Left NoSuchFile)
>         $ parseD s <$> readFile s

The `IO` monad sits at the bottom of a monad transformer stack. However, the `MonadModule`
constraint needs to be visible at the stack's top; we must therefore once again define how `MonadModule`
propagates through the various monad transformers that we will use. The definition
are exceptionally mechanical; all we do is lift the underlying monad's implementation.

> instance MonadModule m => MonadModule (ReaderT r m) where
>     moduleHeader s = lift $ moduleHeader s 
>     moduleContent s = lift $ moduleContent s
>
> instance MonadModule m => MonadModule (ExceptT e m) where
>     moduleHeader s = lift $ moduleHeader s 
>     moduleContent s = lift $ moduleContent s

> instance MonadModule m => MonadModule (PathT m) where
>     moduleHeader s = lift $ moduleHeader s 
>     moduleContent s = lift $ moduleContent s

Finally, let's write some functions to make use of all this machinery.
Since we have commited to using the Linux file separator for our paths,
we'll define a corresponding function to convert a `Symbol` to its
path within a source folder. For instance, `Data.Nat` would correspond
to the `Data/Nat.mp` file.

> symbolFilePath :: Symbol -> String
> symbolFilePath = (++ ".mp") . intercalate "/" . reverse . symbolPath

Finally, let's use all of the above machinery to actually perform IO and
load some modules!

> defaultLoadModule :: Symbol -> IO (Either LoadingError Module)
> defaultLoadModule s = runPathT (runReaderT (runExceptT (loadModule s)) []) ["./stdlib"]

> defaultLoadFile :: String -> IO (Either LoadingError Module)
> defaultLoadFile s = runPathT (runReaderT (runExceptT (loadFile s)) []) ["./stdlib"]
