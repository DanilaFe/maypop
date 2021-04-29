This is a complicated project, and it wouldn't do to not
have any way to verify that everything works. We'll be
using [QuickCheck](https://hackage.haskell.org/package/QuickCheck-2.14.2)
and [HUnit](https://hackage.haskell.org/package/HUnit) to write
some tests, both property-based and unit.

> import Test.QuickCheck.All
> import Test.QuickCheck
> import Test.HUnit
> import Language.Maypop.Syntax
> import Language.Maypop.Checking
> import Language.Maypop.Examples

First, a couple of helper functions. We want to
ensure that a term has a particular type; to this
end, we define two functions, `checkType` (which will
be used for QuickCheck, since `Bool` is `Testable`),
and `assertType` (which will be used for HUnit, since it's just
another assertion).

> checkType :: Term -> Term -> Bool
> checkType t tt = either (const False) (==tt) $ runInfer t
> 
> assertType :: Term -> Term -> Assertion
> assertType t tt = either (const $ assertFailure $ "Inference failed on " ++ show t) (assertEqual "Types need to match." tt) $ runInfer t

Let's start with some property based tests, since they're the most fun.
One of the simplest things we can test is the rule that \\(\\text{Type} \\ n : \\text{Type} \\ (n+1)\\).
Since `Int` has an `Arbitrary` instance, this function forms a `Testable` property.
The integer here is arbitrary; this really reads as "for all integers `i`, ...".

> prop_typeNType :: Int -> Bool
> prop_typeNType i = checkType (Sort $ Type i) (Sort $ Type $ i + 1)

Alas, without a fuzzer, it's hard to get into the meat of property based testing.
We'll have to resort to the "old reliable" hand-written unit tests. We can
start by defining the expected types of some of our examples.

It's best to get started with the various functions we've defined;
not only are they more interesting, but their types are also more
complicated, so if we can get them right, chances are, things
are going pretty well.

Our first test will be the type of `pred_`, the predecessor function for natural numbers.
It has one of the simplest types we'll encounter: \\(\\mathbb{N} \\rightarrow \\mathbb{N}\\).
That is, it takes in a natural number, and returns another natural number.
That, in turn, is just a special case of the product type: \\(\\forall \\ (x : \\mathbb{N}). \\mathbb{N}\\).

> test_predType :: Test
> test_predType = TestCase $ assertType pred_ (Prod (Ind nat) (Ind nat))

The next test is the same function, except this time for
finite natural numbers. In this function, we adjust the upper
bound of the resulting number, since it is, after all, smaller.
However, we can't create a natural number less than zero, so
as input we have to accept a number
{{< sidenote "right" "less-two-note" "less than at least 2." >}}
How do we ensure that a number is less than 2? By forcibly
incrementing our first argument. We will
always have the type <code>Fin (n+2)</code>, and it's not
possible to get a number less than 2 by adding 2 to
a natural number. That's the reason for two applications
of <code>S</code> in our input type.
{{< /sidenote >}}
The type is rather complicated:

\$$
\\forall (n : \\mathbb{N}). \\text{Fin} \\ (S \\ (S \\ n)) \\rightarrow \\text{Fin} (S \\ n)
\$$

> test_predFinType :: Test
> test_predFinType = TestCase $ assertType predFin $ Prod (Ind nat) $ Prod (App (Ind fin) (s $ s $ Ref 0)) $ App (Ind fin) $ s (Ref 1)

This next test checks the type of a function that unwraps an `Either` type whose
two type parameters are the same. It is polymorphic over the type of elements
inside of `Either`, but there's only one type parameter. We expect the
type of the function to be:

\$$
\\forall (\\alpha : \\text{Type 0}). \\text{Either} \\ \\alpha \\ \\alpha \\rightarrow \\alpha
\$$

> test_unwrapEitherType :: Test
> test_unwrapEitherType = TestCase $ assertType unwrapEither $ Prod (Sort $ Type 0) $ Prod (apps (Ind either_) [Ref 0, Ref 0]) $ Ref 1

Next up is a function to "swap" a pair of elements. It has two type parameters, each of
which corresponds to the type of one of the elements of the pair. Once flipped, the pair's
type parameters switch places. The type, then, is:

\$$
\\forall (\\alpha : \\text{Type 0}). \\forall (\\beta : \\text{Type 0}). \\text{Pair} \\ \\alpha \\ \\beta \\rightarrow \\text{Pair} \\ \\beta \\ \\alpha
\$$

> test_swapType :: Test
> test_swapType = TestCase $ assertType swap_ $ Prod (Sort $ Type 0) $ Prod (Sort $ Type 0) $ Prod (apps (Ind pair_) [Ref 1, Ref 0]) $ apps (Ind pair_) [Ref 1, Ref 2]

With the expected types of the functions themselves specified, we can move onto the example
uses of these functions. The first example computes the predecessor of the natural number 3. Its
type, therefore, should just be a natural number, \\(\\mathbb{N}\\). We assert as much.

> test_ex1Type :: Test
> test_ex1Type = TestCase $ assertType ex1 (Ind nat)

The second example applies (the appropriate version of) the predecessor function
to the number 2, the type of which is "less than four". The resulting type
should be a number "less than three".

> test_ex2Type :: Test
> test_ex2Type = TestCase $ assertType ex2 $ App (Ind fin) (n 3)

The third example merely applies the `Either` extraction function to the value `Left 3`. Its type,
therefore, is once again just a natural number, \\(\\mathbb{N}\\).

> test_ex3Type :: Test
> test_ex3Type = TestCase $ assertType ex3 $ Ind nat

The fourth example flips the pair `(3,2)`. The input type is \\(\\text{Pair} \\ \\mathbb{N} \\ \\mathbb{N}\\),
which looks the same with its two type parameters flipped. Our function thus returns a value of type
\\(\\text{Pair} \\ \\mathbb{N} \\ \\mathbb{N}\\).

> test_ex4Type :: Test
> test_ex4Type = TestCase $ assertType ex4 $ apps (Ind pair_) [Ind nat, Ind nat]

Finally, we bundle all our unit tests for types into a single test case:

> test_funcTypes :: Test
> test_funcTypes = TestLabel "Function types." $ TestList
>     [ test_predType, test_predFinType, test_unwrapEitherType, test_swapType ]
> 
> test_exTypes :: Test
> test_exTypes = TestLabel "Example types." $ TestList
>     [ test_ex1Type, test_ex2Type, test_ex3Type, test_ex4Type ]
>
> test_types :: Test
> test_types = TestLabel "Computed types." $ TestList [ test_funcTypes, test_exTypes ]

And execute all the tests using `HUnit`'s `runTestTT`:

> main :: IO Counts
> main = runTestTT $ TestList
>     [ TestCase $ quickCheck prop_typeNType
>     , test_types
>     ]
