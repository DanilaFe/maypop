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
> assertType t tt = either (const $ return ()) (assertEqual "Types need to match." tt) $ runInfer t

Let's start with some property based tests, since they're the most fun.
One of the simplest things we can test is the rule that \\(\\text{Type} \\ n : \\text{Type} \\ (n+1)\\).
Since `Int` has an `Arbitrary` instance, this function forms a `Testable` property.
The integer here is arbitrary; this really reads as "for all integers `i`, ...".

> prop_typeNType :: Int -> Bool
> prop_typeNType i = checkType (Sort $ Type i) (Sort $ Type $ i + 1)

Alas, without a fuzzer, it's hard to get into the meat of property based testing.
We'll have to resort to the "old reliable" hand-written unit tests. We can
start by defining the expected types of some of our examples.

The first example computs the predecessor of the natural number 3. Its
type, therefore, should just be a natural number, \\(\\mathbb{N}\\).
We assert as much.

> test_ex1Type :: Test
> test_ex1Type = TestCase $ assertType ex1 (Ind nat)
>
> test_ex2Type :: Test
> test_ex2Type = TestCase $ assertType ex2 $ Prod (Ind nat) $ Prod (App (Ind fin) (s $ s $ Ref 0)) $ App (Ind fin) $ s (Ref 1)
> 
> test_ex3Type :: Test
> test_ex3Type = TestCase $ assertType ex3 $ Prod (Sort $ Type 0) $ Prod (apps (Ind either_) [Ref 0, Ref 0]) $ Ref 1
> 
> test_ex4Type :: Test
> test_ex4Type = TestCase $ assertType ex4 $ Prod (Sort $ Type 0) $ Prod (Sort $ Type 0) $ Prod (apps (Ind pair_) [Ref 1, Ref 0]) $ apps (Ind pair_) [Ref 1, Ref 2]
> 
> test_ex5Type :: Test
> test_ex5Type = TestCase $ assertType ex5 $ Ind nat
> 
> test_ex6Type :: Test
> test_ex6Type = TestCase $ assertType ex6 $ apps (Ind pair_) [Ind nat, Ind nat]
> 
> test_exTypes :: Test
> test_exTypes = TestLabel "Example typs." $ TestList
>     [ test_ex1Type, test_ex2Type, test_ex3Type, test_ex4Type, test_ex5Type, test_ex6Type ]
> 
> main :: IO Counts
> main = runTestTT $ TestList
>     [ TestCase $ quickCheck prop_typeNType
>     , test_exTypes
>     ]
