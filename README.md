# maypop

This is the repository for the Maypop language. Maypop aims
to be a dependently typed language for verified functional programming.
In addition, it's written using Literate Haskell, and its source code
thus contains a quasi-tutorial on how Maypop works. [Check it out!](https://web.engr.oregonstate.edu/~fedorind/CS583/).

The goal isn't necessarily to make something to replace Coq or Agda, but
to make a language of that sort that is small enough to understand!

Unless something in the pipeline is going wrong, the above link should
be up-to-date with the current commit on this repository.

## What Works So Far
Currently, the Haskell code included can:

* Represent Maypop terms, including inductive data types.
* Evaluate these terms.
* Pretty print the terms.
* Check the types of various terms (without type inference).
* Perform unification (required for type inference).

What still needs to be done:

* Type inference (save users the effort of writing types)
* A module system (to allow imports and abstraction)
* A prelude of common functions
* Tactics to make writing proofs easier
* Type classes (and automatic search for them)

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

## File Structure
There are a lot of files here, but there's some order to this chaos.
Here are the interesting directories:

* `src/` contains the source code for the language itself. If you're from CS 583, that's mostly
where you'll want to look. There, and in the `test/` folder.
* `test/` contains tests (property based and unit) for the language. It is written
in Literate Haskell much like the rest of the project, so hopefully the examples
are somewhat clear.
* `app/` is the (future) location for the Maypop interpreter. Right now, nothing is
there; stay tuned!
* `doc/` contains the various documents we've had to produce for the class.
* `misc/` includes Haskell files that are not strictly relevant to the language,
such as experiments.
* `script/` has the scripts we use to turn the Literate Haskell source code
of Maypop into Hugo-compatible Markdown.
* `content/` is the directory for Hugo content files, written in Markdown.
A handful of these files will be handcrafted (such as the landing page);
the rest, however, will be placed there by the scripts mentioned above.
