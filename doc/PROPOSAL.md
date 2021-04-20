# Maypop Project Proposal
Our project is to implement a dependnetly typed programming languguage called Maypop, based on the Calculus of
Inductive Constructions (the formal model used by Coq). The users of this language would be experienced functional
programmers,who are comfortable with statically typed languages, especially in the Hindley-Milner style. This
language would provide them the ability to express much more complicated properties throguh the type systems, and
construct proofs of various claims about their programs. The initial goal is for Maypop to be an interpreted
language; we are not, at the given time, interested in transalting it into machine code or LLVM IR. Instead,
we'd rather focus on extending the model of the programing language with other, potentially interesting constructs.
Specifically, we'd like to play around with adding linearity / quantification to the type system, so that resource
usage constraints can be more preceisly expressed. Alternatively, since the CIC is explicitly typed, we may
consider extending the language to support (limited) type inference, or a tactic language to simplify writing
proofs. The ultimate stretch goal is to re-implement the language in itself, and possibly prove some properties
about that implementation within the language.

In addition, we'll be experimenting with writing the language in Literate Haskell. This way, rather than writing
comments, we'll be writing a "narrative" to guide the user through the code; this will be additionally supported
through generating a static web site from the descriptions of the code. If all goes well, aside from a programming
language, we'll have a website that serves as a tutorial to implementing your own little Maypop.

# Objects and Concepts
The beauty of the Calculus of Inductive Constructions is that, in a way, there's only one "thing" in the entire
domain: a term. Types are first-class values that can be passed around and manipulated; they are therefore terms.
On the other hand, terms can be used within types (to express, for instance, a "list of length 3"). This
symmetry is rather beautiful, and will be the foundation of our project, via a data type like `Expr`.

The Calculus of _Inductive_ Constructions is extended with _inductive_ data types. These are also terms, but
they are probably interesting enoguh to be described separately. An inductive data type can be _parameterized_
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
  
# Operations

Two closely tied operations in our project will be type checking and type inference.
Typechecking discards invalid terms in the Calculus of Indictive Constructions, but it does not, necessarily, compute types.
Indeed, the type system in CIC is undecideable, and determining a term's type in all cases (without hints
or annotations) is not possible. The core language in CIC requires explicit type annotations, which makes
type checking fairly straightforward, but also complicates writing code in the language. Type _inference_
would make it easier for users to write code by allowing the interpreter to "guess" the types of various terms.
compiler to guess the type of a particular term. In our language, more sohpisticated forms of type inference
can eliminate the need for redundant patterns (a vector of length 1 can't be `Nil`), thus further
reducing additional burden on the user.

Evaluation would also be a core operation in our languge. This is especially so in the Calculus of Inductive Constructions
because _types can depend on terms_. These terms, need not be in normal form; it is entirely possible to have
something along the lines of `Vector Int (length xs)`. To correctly compute the type, it's necessary to be able
to evaluate the expression `length xs`. Of course, even outside of type checking, for our language to be useful,
we'd need to support evaluating expressions, likely from a text file; what good is a language you can't
actually interpret?

# Course Ideas
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
