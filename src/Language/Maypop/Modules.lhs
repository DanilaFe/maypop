In this (Haskell) module, we'll define (Maypop) modules.

> {-# LANGUAGE FlexibleContexts #-}
> module Language.Maypop.Modules where
> import Language.Maypop.Syntax
> import Control.Monad.Except
> import Control.Monad.Writer
> import Data.List
> import Data.Maybe
> import qualified Data.Map as Map

We'll go for a module system similar to that of Haskell. In particular:

* Each file will contain exactly one module. The module name will be
provided at the top of the file; if it is _not_ provided, the default
module name `Main` will be used.
* Modules will be able to export the definitions within them. Just like
Haskell, we'll be able to export data types, their constructors, and
function definitions. It will be possible to export a data type without
exporting its constructors.
* When importing a module, its exports will become available in
the current module. If there are two overlapping names from two
imported modules, they are to be disambiguated by their qualified
(including module path) name.
* If a module's name is too long, it can be adjusted when it is imported.
* If the user wants, they can force the definitions in an entire module they
are importing to be qualified.
* It is possible to import a module multiple times. For instance, importing
the entire thing qualified under a shorter path name, and then also importing
some important function unqualified.

We appear to have our work cut out for us! The first thing we can define
is a data structure for (posibly qualified) names of definitions. Let's
call it `Symbol`. This will be a simple list of strings, but with
a little gotcha: the name `Module.function` will be represented as
`MkSymbol ["function", "Module"]`. This way, it's easier to append
strings to the end of symbol: we can just ue `(:)` on the `symbolPath` field.

> newtype Symbol = MkSymbol { symbolPath :: [String] } deriving (Eq, Ord)

With a `Symbol` data type in place, we can define a few helpers for
creating it from strings, and appending strings to it.

> qualName :: Symbol -> String -> Symbol
> qualName sm s = MkSymbol $ s : symbolPath sm
>
> unqualName :: String -> Symbol
> unqualName = MkSymbol . return

We can quickly define a show instance, too:

> instance Show Symbol where
>     show MkSymbol{symbolPath=sp} = intercalate "." $ reverse sp

Retrieving the human-readable module name requires reversing the list; however,
given that we save time prepending (and that we don't usually need
to retrieve the human-readable version of the string), this seems like
a good aproach. 

Next up, let's define a data type for definition visibility. We'll have
some kind of mechanism in our syntax for specifying whether or not a definition
is public or private; this will affect whether or not it can be exported by a module.

> data Visibility = Private | Public deriving Eq
>
> isPublic :: Visibility -> Bool
> isPublic Public = True
> isPublic Private = False

Let's also define a (Haskell) data type that can hold either a (Maypop) data type
definition or a (possibly fixpoint) function definition. This data type will also include visibility
information. 

> data DefinitionContent 
>     = IndDef Inductive
>     | FunDef Function
>     | FixDef Fixpoint
>
> asFunction :: DefinitionContent -> Maybe Function
> asFunction (FixDef f) = Just $ fxFun f
> asFunction (FunDef f) = Just f
> asFunction _ = Nothing
>
> data Definition = Definition
>     { dVisibility :: Visibility
>     , dContent :: DefinitionContent
>     }

Both types of definitions have names; however, they are part of their
own data structure. We can define a convenience function to extract
the name of a definition, be it a function or an inductive definition.

> dName :: Definition -> String
> dName Definition{dContent=IndDef i} = iName i
> dName Definition{dContent=FunDef f} = fName f
> dName Definition{dContent=FixDef f} = fName (fxFun f)

Finally, let's define a representation for a module:

> data ModuleHeader = ModuleHeader
>     { mhName :: Symbol
>     , mhImports :: [(Symbol, ModuleImport)]
>     }

> data Module = Module
>     { mHeader :: ModuleHeader
>     , mDefinitions :: Map.Map String Definition
>     }
>
> mName :: Module -> Symbol
> mName = mhName . mHeader
>
> mImports :: Module -> [(Symbol, ModuleImport)]
> mImports = mhImports . mHeader

Given such a module, it would be useful to retrieve all the
definitions that can be exported; we will use this when importing
functions and data types from the module. 

> visibleDefs :: Module -> Map.Map String Definition
> visibleDefs = Map.filter (isPublic . dVisibility) . mDefinitions

With that out of the way, let's define a data structure to keep track
of all the definition available in the current scope. We'll track of this two
ways. First, there will be a one-to-one map of _fully qualified names_, like `List.map`.
Duplicates should not be allowed here; a module cannot export the same name multiple
times, and two modules should not be called the same thing. Second, there will
be a one-to-many map of _unqualified_ names, like `map` (which may refer to,
say, to the `map` function
{{< sidenote "right" "typeclass-note" "for lists or sets" >}}
We are ignoring, for the moment, that Maypop intends to implement
type classes, which would make <code>map</code> mean the same
thing for both lists and sets.
{{< /sidenote >}}). Duplicates will be allowed here, and we'll use 
this map to report errors in the case of ambiguous definitions.

But what should the maps be _of_? We could try to export `Definition`s,
but things get awkward when we realzie that constructors are another
thing that may or may not be exported, but is part of the `Inductive`
definition. It would be a pain to carry the information about whether
an inductive type's constructors are publically visible everywhere
throughout our program. Instead, we'll define a "thing", `Export`,
which represents _something_ that a module may provide.
For cases in which two imported modules export the same "thing"
(which can occur if one module re-exports another), we include the name of the
module in which the "thing" was created; this will help us merge two intances
of the same definition into one.

> data Export = Export
>     { eVariant :: ExportVariant
>     , eOriginalModule :: Symbol
>     }
>
> data ExportVariant
>     = IndExport Inductive
>     | ConExport Inductive Int
>     | FunExport Function
>     | FixExport Fixpoint

With that, we go ahead and define our two-map `GlobalScope`.

> data GlobalScope = GlobalScope
>     { sQualified :: Map.Map Symbol Export
>     , sUnqualified :: Map.Map Symbol [Export]
>     }

Given a module, we can compute the scope provided _only_ by that module.
For this, we need data about how this module was imported: what definitions
were required, whether or not it was imported qualified, and what its
requested (possibly adjusted) name is. For this, we define another data structure:

> data ModuleImport = ModuleImport
>     { miQualified :: Qualified
>     , miNames :: Map.Map String ImportType
>     , miName :: Maybe Symbol
>     }

In the above snipped, we used two new data types. The first is merely
a custom boolean value, `Qualified`, which determines whether or not
a module is imported qualified or not.

> data Qualified = Qualified | NotQualified

Next up is `ImportType`. It is also effectively a boolean. We use this
because we want to allow a distinction between importing just a data type
(and not its constructors), or importing a data type _and_ its constructors.
The former would be written like `List`, and the latter as `List(..)`.

> data ImportType = Open | Closed

Now, given a module, we can compute the data it adds to the current scope.
This may not work; for instance, it may be that we try to import something
that isn't there, or something that's marked as private. Another possible
error is that we try to openly import a thing that's not an inductive definition -
what does that even mean?! We do, however, __assume that
the module is well-formed here__, and therefore that there aren't duplicate
definitions.

> data ImportError
>     = NotExported
>     | BadOpenImport
>     | DuplicateQualifiedName
>     deriving Show

Finally, let's get to the meat of importing a module. Here we will
once again use the MTL. We'll take advantage of `Either`'s implementation
of `MonadError`, using it to keep track of any possible issues that may
come up while trying to import a module. We will also take advantage
of the fact that `Map` is a monoid 
{{< sidenote "right" "biased-note" "(presumably under left-biased union)." >}}
It doesn't actually matter in our case if the union is left- or right-biased.
Since we have assumed the well-formedness of the input <code>Module</code>,
we have also assume that there would be no conflicting names; thus, there
are no conflicts which need bias to be resolved.<br><br>
Another reason that we want well-formedness here is that if we were to
properly keep track of the lists of unqualified definitions with the same
name, we'd need to <em>read</em> the current state instead of just
writing to it, which woul force us into using <code>MonadWriter</code>.
{{< /sidenote >}} Then, we emit (via `tell`) new exports as `Map.singleton`
instances, which get automatically combined with all of the previously-emitted
exports.

> moduleScope :: ModuleImport -> Module -> Either ImportError GlobalScope
> moduleScope mi m = uncurry GlobalScope . snd <$> runWriterT (mapM_ processImport names)
>     where
>         actualName = fromMaybe (mName m) (miName mi)
>         names = Map.toList $ miNames mi
>         defs = visibleDefs m
>         tellExport n ev = tell (qualMap, unqualMap)
>             where
>                 export = Export ev (mName m) 
>                 qualMap = Map.singleton (qualName actualName n) export
>                 unqualMap = Map.singleton (unqualName n) [export]
>         tellCon i ci c = tellExport (cName c) (ConExport i ci)
>         processImport (n, it) = do
>             def <- maybe (throwError NotExported) return $ Map.lookup n defs
>             case (it, dContent def) of
>                 (Open, IndDef i) -> do
>                     tellExport n (IndExport i)
>                     mapMWithIndex (tellCon i) $ iConstructors i
>                 (Closed, IndDef i) -> tellExport n (IndExport i)
>                 (Closed, FunDef f) -> tellExport n (FunExport f)
>                 (Closed, FixDef f) -> tellExport n (FixExport f)
>                 (Open, _) -> throwError BadOpenImport

For the above, we use a little utility, `mapMWithIndex`, which is a version
of [`mapM`](https://hackage.haskell.org/package/base-4.15.0.0/docs/Prelude.html#v:mapM)
that also accepts an index (like `mapWithIndex`).

> mapMWithIndex :: Monad m => (Int -> a -> m b) -> [a] -> m ()
> mapMWithIndex f xs = mapM_ (uncurry f) $ zip [0..] xs

So now we have a way to collect the exports from a single import. What about multiple imports?
We'll need to combine them, returning errors if there are conflicts of fully qualified names.
These errors are actually why we shouldn't define a `Monoid` instance for `GlobalScope`:
the type `a -> a -> a` is not amenable to reporting error messages. Intead, we define
our own function:

> mergeScopes :: GlobalScope -> GlobalScope -> Either ImportError GlobalScope
> mergeScopes gs1 gs2 = flip GlobalScope unqualified <$> qualified
>     where
>         unqualified = Map.map (nubBy sameOriginalMod)
>             $ Map.unionWith (<>) (sUnqualified gs1) (sUnqualified gs2)
>         qualified = Map.fromList <$> mapM combineQualified qualifiedKeys
>         qualifiedKeys = nub $ Map.keys (sQualified gs1) ++ Map.keys (sQualified gs2)
>         combineQualified k =
>             case (Map.lookup k $ sQualified gs1, Map.lookup k $ sQualified gs2) of
>                 (Just e1, Just e2) | sameOriginalMod e1 e2 -> return (k, e1)
>                 (Just e1, Nothing) -> return (k, e1)
>                 (Nothing, Just e2) -> return (k, e2)
>                 _ -> throwError DuplicateQualifiedName
>         sameOriginalMod e1 e2 = eOriginalModule e1 == eOriginalModule e2

As an identity element for `mergeScopes`, let's define `emptyScope`:

> emptyScope :: GlobalScope
> emptyScope = GlobalScope Map.empty Map.empty

Unqualified names, which may well have duplicates, are combined using `mappend`,
but deduplicated (to make sure the same definition, when imported twice, doesn't break
anything). Qualified names, on the other hand, are compared with an `Either`-returning
function, which produces a "failing" result when two exports originating from differing modules
are mapped to the same qualified name.

