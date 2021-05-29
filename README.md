# maypop

This is the repository for the Maypop language. Maypop aims
to be a dependently typed language for verified functional programming.
__In addition, it's written using Literate Haskell, and its source code
thus contains a quasi-tutorial on how Maypop works. [Check it out!](https://web.engr.oregonstate.edu/~fedorind/CS583/).__

The goal isn't necessarily to make something to replace Coq or Agda, but
to make a language of that sort that is small enough to understand!

Unless something in the pipeline is going wrong, the above link should
be up-to-date with the current commit on this repository.

## What Works So Far
Currently, the Haskell code included can:

* Represent Maypop terms, including inductive data types (GADTs).
* Evaluate these terms.
* Pretty print the terms.
* Check the types of various terms (without type inference).
* Perform unification (required for type inference).
* Parse a (currently ugly) syntax for the language
* Organize code into modules and import required definitions
* Typecheck modules.

Using Maypop, we were able to define the addition of natural
numbers, and __prove the following properties about it__:

* `0 + n = n`. This follows immediately from the definition of addition,
and is not particularly interesting.
* `n + 0 = n`. This does _not_ immediately follow from the 
definition of addition, and needs to be proved by induction.
* `(1 + n) + m = n + (1 + m)`, which is a lemma used for the proof of...
* `n + m = m + n`, also known as commutativity of addition!

What still needs to be done:

* Type inference (save users the effort of writing types)
* Tactics to make writing proofs easier
* Type classes (and automatic search for them)

## Design Decisions

* Represent unification as a monad transformer (`MonadUnify` and `UnifyT`).
Instead of writing a special purpose function for unifying terms, we have
put this functionality into a general monad transformer (one that requires
`MonadlAlternative` on the underlying monad). This was made to improve
the reusability of the code; while type inference relies on unification,
so does logic programming, and our type class instance search seems to be
(at least in simple cases) reducible to a Prolog-like database search.
We can mix in `LogicT` (from a paper by Oleg Kieselov) for backtracking,
and implement a prolog-like language in 50 extra lines!
* Use MTL style as much as possible. This helps us avoid a _lot_ of extra
code; we hide away a lot of the "plumbing" like environments and common
variables via `MonadReader`, handle errors via `MonadError`, and so on.
By using the MTL style of introducing constraints onto a monadic type
variable, we're able to make our code work in more contexts
(for instance, we were able to swap out unification mechanisms in
the type inference code with virtually no changes to the inference
code itself), and to add various effects (such as unification)
with very little effort. By abstracting the common set of type
classes into a "synonym" class (like `MonadInfer`), we're able
to further clean up our type signatures and simplify refactoring.
* `IO` hardly occurs in our code; we even define special monad instances
like `MonadPath` for computations that can be used to interact with the
filesystem. We thus separate ourselves as much as possible from the concerns
of impurity, and can focus on the purely functional "core" of our
application. Furthermore, this would allow us to perform additional
testing on our code by mocking the results of I/O actions: we can,
for instance, write a custom instance of `MonadModule`, which
would return predefined modules instead of trying to read from disk.

## Running
The project is built using Stack. Thus, to enter GHCi with
all of the relevant code, simply run:

```
stack ghci
```

To run our (currently minimal) test suite, run:

```
stack test
```

The test suite is currently the best place to look for example
inputs. Check out the [`Spec`](https://web.engr.oregonstate.edu/~fedorind/CS583/modules/spec/)
page, which includes not only the Haskell representation of various example
terms, but also explanations on why these terms have particular types.
It even has neatly rendered mathematical notation! If the page is down,
the `Spec.lhs` file in `src/` will include the same information (albeit in
a less pretty format).

Other that that, we also have a barebones application that loads a Maypop
file and typechecks it. For instance, you can run:

```
stack run stdlib/Data/Pair.mp
```

This will load the file `stdlib/Data/Pair.mp`, and print all the function
that are defined with it. If the module contains errors, the error will
be printed instead. You can define your own modules anywhere; however,
if you import anything in that module file, the interpreter will
only search the `stdlib` folder. For example, importing `Data.Bool`
will search `stdlib/Data/Bool.mp`.

## File Structure
There are a lot of files here, but there's some order to this chaos.
Here are the interesting directories:

* `src/` contains the source code for the language itself. If you're from CS 583, that's mostly
where you'll want to look. There, and in the `test/` folder.
* `test/` contains tests (property based and unit) for the language. It is written
in Literate Haskell much like the rest of the project, so hopefully the examples
are somewhat clear.
* `app/` is the location for the Maypop interpreter. Right now, only a barebones
file loader is there. Stay tuned!
* `doc/` contains the various documents we've had to produce for the class.
* `misc/` includes Haskell files that are not strictly relevant to the language,
such as experiments.
* `script/` has the scripts we use to turn the Literate Haskell source code
of Maypop into Hugo-compatible Markdown.
* `content/` is the directory for Hugo content files, written in Markdown.
A handful of these files will be handcrafted (such as the landing page);
the rest, however, will be placed there by the scripts mentioned above.
