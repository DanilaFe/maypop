## Maypop Project Proposal
Our project is to implement a dependently typed programming language called Maypop, based on the Calculus of
Inductive Constructions (the formal model used by Coq). The users of this language would be experienced functional
programmers, who are comfortable with statically typed languages, especially in the Hindley-Milner style. This
language would provide them the ability to express much more complicated properties through the type systems, and
construct proofs of various claims about their programs. The initial goal is for Maypop to be an interpreted
language; we are not, at the given time, interested in translating it into machine code or LLVM IR. Instead,
we'd rather focus on extending the model of the programing language with other, potentially interesting constructs.
Specifically, we'd like to play around with adding linearity / quantification to the type system, so that resource
usage constraints can be more precisely expressed. Alternatively, since the CIC is explicitly typed, we may
consider extending the language to support (limited) type inference, or a tactic language to simplify writing
proofs. The ultimate stretch goal is to re-implement the language in itself, and possibly prove some properties
about that implementation within the language.

In addition, we'll be experimenting with writing the language in Literate Haskell. This way, rather than writing
comments, we'll be writing a "narrative" to guide the user through the code; this will be additionally supported
through generating a static web site from the descriptions of the code. If all goes well, aside from a programming
language, we'll have a website that serves as a tutorial to implementing your own little Maypop.

## Example
Below are some example of (hypothetical) code in the Maypop language.
First and foremost, the Peano encoding of natural numbers. Here,
`O` represents zero, and `S n` represents the successor of `n`,
aka `n+1`. Any natural number can be built using these constructors.

```
data Nat : Type 0 where
   O : Nat 
   S : Nat -> Nat    
```

Notice `Type 0`. This is the type of types in the Calculus of Inductive Constructions.
The number is there because this type, too, is an expression in the language
(for instance, we can write `\x -> Type 0`), and must therefore itself have a type.
The type of `Type 0` is `Type 1`. By a similar logic, `Type 1` has type `Type 2`,
and so on.

So far, we saw a data type definition that's actually possible in Haskell, too.
The interesting features of our language come in when _types start depending on
values_. A very interesting example is the `Fin` type constructor. Here's
how it would be defined in Maypop:

```
data Fin : Nat -> Type 0 where
    FO : forall (n : Nat). Fin (S n)
    FS : forall (n : Nat). Fin n -> Fin (S n)
```

This defines a type family _indexed by natural numbers_. That is, `Fin O` and
`Fin (S O)` are different types, and mean different things. But note, though,
that these types _contain values_! `O` and `S O` are values of type `Nat`. In this
context, `Fin n` reads as "a natural number that's less than n". Thus,
`F0` is a natural number less than any positive natural number, and `FS`,
which is equivalent to the successor function for natural numbers, takes
a number less than `n` and returns a number less than `n+1` (since `x < n`
is the same as `x + 1 < n + 1`). It's not clear why this is useful just yet;
however, let's also define a list data type using the same strategy as we used
for `Fin`:

```
data List (A : Type 0): Nat -> Type 0 where
    Nil : List A O
    Cons : forall (n : Nat). A -> List A n -> List A (S n)
```

The type `List A n` now means, "a list of values of type A, of length n".
Then, the constructors start making sense: `Nil` creates a list
of any type `A` whose length is zero, and `Cons`, for any size
`n`, takes a value of type `A`, a list of `A`s of size `n`,
and returns a list of `A`s of size `n+1` (which makes sense, since
`Cons` adds one element to the list). Finally, we can define
a function that returns an element from a list at a certain index:

```
elemAt : forall (a : Type 0). forall (n : Nat). Fin n -> List a n -> a
elemAt FO     (Cons x _ ) = x
elemAt (FS f) (Cons _ xs) = elemAt f xs
```

Importantly, notice that there's no case for `Nil`! `Nil`
would have the type `List a O`, which means that the first
argument would have to have type `Fin O`. But there's no
natural number less than zero, so this is impossible! We
have actually written a function _that's guaranteed to
work if it typechecks_. There's no need for throwing
exceptions (like Haskell's `(!!)` function), nor for
returning `Maybe a`. Everything is type safe!

In particular, we're interested in making Maypop a language
__for verified functional programming__. The Calculus of Inductive
Constructions is particularly amenable to this application, because
its type system corresponds to a sizeable subset of [intuitionistic
logic](https://plato.stanford.edu/entries/logic-intuitionistic/)
via the [Curry-Howard correspondence](https://en.wikipedia.org/wiki/Curry–Howard_correspondence).
Although sophisticated proofs are possible in the framework, writing
them is rather cumbersome without additional support. For instance,
here's a proof of the commutativity of the additional of natural
numbers in the Coq language (taken from the C-H correspondence
link above):

```Coq
plus_comm =
fun n m : nat =>
nat_ind (fun n0 : nat => n0 + m = m + n0)
  (plus_n_0 m)
  (fun (y : nat) (H : y + m = m + y) =>
   eq_ind (S (m + y))
     (fun n0 : nat => S (y + m) = n0)
     (f_equal S H)
     (m + S y)
     (plus_n_Sm m y)) n
     : forall n m : nat, n + m = m + n
```

To assist in writing proofs, it's possible to use _tactics_.
Using tactics, the above proof can be rewritten as:

```Coq
intros n m.
induction n as [|n' IH]; simpl.
- apply plus_n_O.
- rewrite <- plus_n_Sm.
  rewrite -> IH.
  reflexivity.
```

In our opinion, the second version is far clearer:
the proof proceeds by induction, using the claim `plus_n_O`
that `n + 0 = n` in the base case, and invoking
the inductive hypothesis `IH` in the recursive case.
We aim to also add Coq-like tactics to Maypop to make
similarly simplify the verified functional programming
experience in the language.

## Objects and Concepts
The beauty of the Calculus of Inductive Constructions is that, in a way, there's only one "thing" in the entire
domain: a term. Types are first-class values that can be passed around and manipulated; they are therefore terms.
On the other hand, terms can be used within types (to express, for instance, a "list of length 3"). This
symmetry is rather beautiful, and will be the foundation of our project, via a data type like `Expr`.

The Calculus of _Inductive_ Constructions is extended with _inductive_ data types. These are also terms, but
they are probably interesting enough to be described separately. An inductive data type can be _parameterized_
and _indexed_ by different terms, forming a type constructor [^1]. For instance, `Maybe` is parameterized
by the type of the item inside of it (for instance, `User` or `String`), while `Vector` is parameterized
by the type of its elements, and indexed by its length. An inductive data type consists of the following
elements:

* **The parameters**: things that are the same for each constructor, and don't affect the structure of the data 
* **The "arity"**: the _types_ of the indices to the type constructor that differ depending on the structure of the data.
* **The constructors**: ways of constructing the data type, which may accept arguments (like `x` and `xs` in `Cons`),
  and produce an instance of the inductive data type with some concrete indices.
  
The constructors of a data type, since they have a list of parameters, and produce a type indexed by some terms,
can also be considered to be objects in our language.
  
## Operations

Two closely tied operations in our project will be type checking and type inference.
Type checking discards invalid terms in the Calculus of Inductive Constructions, but it does not, necessarily, compute types.
Indeed, the type system in CIC is undecidable, and determining a term's type in all cases (without hints
or annotations) is not possible. For more examples of type checking, please see [our Literate Haskell
page for the `Spec` module](https://web.engr.oregonstate.edu/~fedorind/CS583/modules/spec/).

The core language in CIC requires explicit type annotations, which makes
type checking fairly straightforward, but also complicates writing code in the language. Type _inference_
would make it easier for users to write code by allowing the interpreter to "guess" the types of various terms.
In our language, more sophisticated forms of type inference
can eliminate the need for redundant patterns (a vector of length 1 can't be `Nil`), thus further
reducing additional burden on the user. As an example of type inference, consider the `swap` function
that turns pairs like `(3, "Hello")` into `("Hello", 3)`. In Haskell, `swap (3, "Hello")` will
type check successfully, since Haskell can infer the type parameters for `swap`. However,
without type inference, in our language, you'd have to write `swap Nat String (3, "Hello")`. 
By including type inference, we'd make our programs look more like the Haskell versions.

Evaluation would also be a core operation in our language. This is especially so in the Calculus of Inductive Constructions
because _types can depend on terms_. These terms, need not be in normal form; it is entirely possible to have
something along the lines of `Vector Int (length xs)`. To correctly compute the type, it's necessary to be able
to evaluate the expression `length xs`. Of course, even outside of type checking, for our language to be useful,
we'd need to support evaluating expressions, likely from a text file; what good is a language you can't
actually interpret?

## Course Ideas
I think most of all we'll be using Monads and Monad Transformers. Various operations in our language will require
context (`Reader` monad), modify state (`State` monad) or fail (`Exception` monad). Additionally, things like
unification and backtracking can be represented monadically too. It would be very convenient to use something
like the MTL to compose the various effects required for our language, and, as far as I know, this will
be taught by the course.

Curiously, the language we _implement_ will have GADTs, as implemented by inductive data types.
Should we attempt to achieve our goal of self-hosting the language, we'll likely make use of GADTs
to define the syntax of our terms, potentially requiring the expression type to be correct by construction.
For instance, we may define the (meta) type of an inductive (object) type to be indexed by the number
of constructors it has; then, the representation of a constructor of this type will simply be a bounded natural number
referring to a constructor in the list. This natural number will be _required_, by the type, to
refer to a constructor inside the list, and not beyond it. It's difficult to implement this
in pure Haskell with only GADTs, type families, and phantom types; in a dependently-typed language,
though, this idea seems both useful and fairly easy.


[^1]: https://stackoverflow.com/questions/24600256/difference-between-type-parameters-and-indices
