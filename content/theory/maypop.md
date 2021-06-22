---
title: "Introduction to Maypop"
date: 2021-05-29T01:05:30-07:00
draft: true
---

Languages with dependent types have been around for some time. [Coq](https://coq.inria.fr/), which was used
to implement a [verified compiler for the C language](https://compcert.org/), was initially
released in 1989. [Agda](https://agda.readthedocs.io/en/v2.6.2/getting-started/what-is-agda.html),
which some seem to find more useful for [teaching programming languages](https://plfa.github.io/),
originally appered in 1999. [Idris](https://www.idris-lang.org/), which focuses more
on _programming_ with dependent types, was developed around 2007. Indeed, the __youngest__
of these languages came into being when I was no older than 7 years old, and far from
being able to even understand what a "programming language" was. It follows, then,
that Maypop does not bring any new theory to the table.

My goal with the Maypop was, instead, to provide a small and simple _implementation_ of
a dependently typed language. I do not expect the language to garner any amount
of adoption, and certainly not compte with the _grosses légumes_ I mentioned above.
However I hope that, together with some commentary, the code base can help demystify
how such a language might work. This is why all of Maypop is written in Literate Haskell,
and displayed on this website: it's a learning resource.

Despite Maypop's consequent status as a mere object language, I think that it may be useful
to begin by looking at its syntax and (informal) semantics. What better way is there to introduce
dependent types and a language that uses them? It should be noted, though, that this guide
assumes a familiarity with the lambda calculus, as well as [System F](https://en.wikipedia.org/wiki/System_F),
which is the formal model underlying Haskell.

### Identity Function

Probably the simplest function in the lambda calculus is the identity function; it takes an argument,
and returns it. If we were to write such a function without types, we might produce \\(\\lambda x. x\\).
However, we're looking at _typed_ languages, and, starting with only lambda functions (and the
type \\(\\mathbb{N}\\) of natural numbers), we might write the identity function as
\\(\\lambda x:\\mathbb{N}. x\\). If, on the other hand, we wanted booleans, we might instead write
the identity function as \\(\\lambda x:\\mathbb{B}. x\\). The functions have types
\\(\\mathbb{N}\\rightarrow\\mathbb{N}\\) and \\(\\mathbb{B}\\rightarrow\\mathbb{B}\\), respectively.
This same pattern can be repeated for any other type.

But hold on a minute, that's kind of ugly! Our functions are identical, save for a single type
annotation. We as programmers don't like repeating ourselves, and seek to abstract repeating patterns.
System F gives us a way to do this by introducing another language construct: a \\(\\Lambda\\)-abstraction,
which introduces variables ranging over _types_, rather than _values_. We can implement a general identity
function by first accepting the type of the argument, and then the argument itself:

{{< latex >}}
\Lambda \alpha. \lambda x:\alpha. x
{{< /latex >}}

What is the type of such a function? It's fairly easy to see that we can't define it using
\\((\\rightarrow)\\); even if we could write something like \\(\\text{Type}\\rightarrow\\tau\\)
(which we can't, since \\(\\text{Type}\\) is not, itself, a type), we'd have no way to refer
to this type in the function's return type \\(\\tau\\). Thus, together with \\(\\Lambda\\)-abstraction,
we introduce a new form of types. The new identity function, together with its type, is as follows:

{{< latex >}}
\Lambda \alpha. \lambda x:\alpha. x : \forall \alpha. \alpha \rightarrow \alpha
{{< /latex >}}

The new form \\(\\forall\\) allows us to accept a type parameter \\(\\alpha\\), and also to return a value
of a type that can depend on \\(\\alpha\\\). In this sense, we have __values depending on types__
(this is _not_ an instance of a dependent type, though, in which this dependency is reversed).

### Something More General?

Let's take a detour and look at the _inference rules_ that define the types of System F,
some of which come directly from the simply typed lambda calculus. Type rules are in the form
\\(\\Gamma\\vdash e : \\tau\\), which reads "the expression \\(e\\) has type \\(\\tau\\) in the
environment \\(\\Gamma\\)". The environment is needed because a variable, like \\(x\\), can have
a different type depending on what was previously assigned to it. Now, back to the rules.
One of the rules of System F is that for \\(\\lambda\\)-abstraction:

{{< latex >}}
\frac
    {\Gamma,x:\tau'\vdash e:\tau}
    {\Gamma\vdash \lambda x:\tau'. e : \tau' \rightarrow \tau}
{{< /latex >}}

The above rule reads: if the body of the lambda abstraction, \\(e\\),
given access to a variable \\(x\\) of type \\(\\tau'\\) and all
the other previously available variables, has type \\(\\tau\\),
then a lambda abstraction has type \\(\\tau'\\rightarrow\\tau\\).
Notice the pattern: the type \\(\\tau'\\) of the parameter \\(x\\) is added to the environment
to determine the type \\(\\tau\\) of the body \\(e\\). Subsequently, \\(\\tau\\) becomes the return type of a function. 
Of course, corresponding to the rule for abstraction, there is also
the rule for application:

{{< latex >}}
\frac
    {\Gamma\vdash e_1:\tau' \rightarrow \tau \quad \Gamma\vdash e_2:\tau'}
    {\Gamma\vdash e_1\; e_2 : \tau}
{{< /latex >}}

Informally, it reads: given a function of type \\(\\tau' \\rightarrow \\tau\\),
and an argument of a matching type \\(\\tau'\\), we can apply the function,
receiving some result of type \\(\\tau\\). Notice the pattern here, too: for some
function accepting a type \\(\\tau'\\), we require a matching argument, and return
the result of type \\(\\tau\\), the right-hand part of the function's type. With the two patterns, one for application
and one for abstraction, in mind, let's move on to the rules governing
the equivalent mechanisms for types. First, the case for \\(\\Lambda\\)-abstraction:

{{< latex >}}
\frac
    {\Gamma,\alpha\ \text{type}\vdash e:\tau}
    {\Gamma\vdash \Lambda \alpha. e : \forall \alpha. \tau}
{{< /latex >}}

Here, \\(\\alpha\\) is not quite a variable, so its addition to the environment
looks a little bit different (via the \\(\\text{type}\\) keyword). So too
is the type of the whole expression different,
{{< sidenote "right" "renaming-note" "since it contains \(\alpha\)." >}}
A subtlety here is that for this to work, the type \(\forall \alpha. \tau\) need not
actually have the same variable name as the \(\Lambda\)-abstraction itself.
Just as \(\lambda x.x\) and \(\lambda y.y\) mean the same thing, so do
\(\forall \alpha. \alpha\) and \(\forall \beta. \beta\).
{{< /sidenote >}}
However, the earlier pattern remains: the type of the body becomes
the return type of \\(\\forall \\alpha. \\tau\\), and when the body's
type is checked, the environment is
{{< sidenote "left" "valid-note" "extended with the abstraction's parameter." >}}
Why do we need to extend the environment with the type parameter here?
Because a lambda abstraction in the form \(\lambda x : \tau'. e\) is
only valid if all the type variables in \(\tau'\) were introduced by
a surrounding \(\Lambda\) abstraction. That is, \(\Lambda \alpha. \lambda x:\alpha.x\) is
valid, but \(\lambda x:\alpha. x\) by itself is not.
{{< /sidenote >}}
Now, let's look at applying a polymorphic function to a type:

{{< latex >}}
\frac
    {\Gamma\vdash e:\forall \alpha. \tau}
    {\Gamma\vdash e\; [\tau'] : \tau[\tau'/\alpha]}
{{< /latex >}}

The curiosity here is that the type \\(\\tau'\\), which serves
as the application's argument, escapes the realm of expressions,
and appears on the right side of the \\(:\\), in the expression's type.
The notation \\(e[\\tau'/\\alpha]\\) here means substitution, specifically
the substitution of the type \\(\\tau'\\) for \\(\\alpha\\).
Thus, the application \\(\\text{id}\\ [\\mathbb{N}]\\) would have type
\\((\\alpha\\rightarrow\\alpha)[\\mathbb{N}/\\alpha] = \\mathbb{N}\\rightarrow\\mathbb{N}\\), as expected.
Notice that here, too, the pattern is repeated: we have an application of an
expression expecting a type, to a matching argument (a type). The result
is the "right hand side" of the type, although in this case it also undergoes
substitution.

Did I mention earlier that as programmers, we love abstracting patterns? The
repetition here seems to hint at a more general principle, and indeed there is one.
However, the two rules are obviously different: one performs substitution, and the other does not.
Surely, though, we can't force our type application not to perform substitution.
As we just saw above, that was a key component to make the type of \\(\\text{id}\\ [\\mathbb{N}]\\)
work out! Regardless, bringing others down to the lowest common denominator,
in the style of _Harrison Bergeron_, is not the way to go. Perhaps, instead,
we can endow regular abstraction with the same substitution mechanism? Why
would we ever want something like that?

### A Taste of Dependent Types

Let's draft a new rule for function application that can perform substitution.
We need an analog to our \\(\\forall\\) type (since it contains a name,
while regular \\(\\tau'\\rightarrow\\tau\\) functions do not). It's usual
in other literature to use the symbol \\(\\Pi\\) for this purpose. Our new construct
then has the form \\(\\Pi x:\\tau'. \\tau\\), which is _almost_ like a function
from \\(\\tau'\\) to \\(\\tau\\), except that the argument, named \\(x\\),
can occur in \\(\\tau\\). Then, our application rule looks like:

{{< latex >}}
\frac
    {\Gamma\vdash e_1: \Pi x:\tau'. \tau \quad \Gamma\vdash e_2:\tau'}
    {\Gamma\vdash e_1\; e_2 : \tau[e_2/x]}
{{< /latex >}}

Wait a moment! Last time, the type \\(\\tau'\\) made the jump between
the realm of expressions and the realm of types. This was fine,
though: it was a "type in a type's world". This time, however,
we have an expression, \\(e_2\\), being substituted inside our
type \\(\\tau\\). This expression can be anything: a number, a list,
a function. Do we really want our types to contain such things?

Well, here's one example when we might. Consider the function:

{{< latex >}}
\text{nthElem} : \forall \alpha. \mathbb{N} \rightarrow [\alpha] \rightarrow \text{Maybe}\ \alpha
{{< /latex >}}

The use of \\(\\text{Maybe}\\) is required here because we may well give the
function a natural number that's larger than the length of the list. We
can't return a corresponding element, and thus, we'd have to resort to
\\(\\text{Nothing}\\). However, what if we wanted to write an expression like:

{{< latex >}}
\text{nthElem}\ [\mathbb{N}]\ 0\ [1,2,3]
{{< /latex >}}

It's obvious that this operation is safe: we _know_ that the list is
not empty! However, we'd still be handed a \\(\\text{Maybe}\\ \\mathbb{N}\\),
and have to deal with unwrapping it. Lame! What if instead, our list type
carried with it the information about how many elements are contained
within? We could write the type of \\([1,2,3]\\) as something like
\\(\\text{Vec}\\ \\mathbb{N}\\ 3\\), a _vector_ of length 3. The use of
{{< sidenote "right" "version-note" "a version of \(\text{nthElem}\)" >}}
I don't present the type of this version here since we do not yet
know how to encode the notion of a number less than some other number.
{{< /sidenote >}}
on this type would only be type correct if the argument
was guaranteed to be less than the vector's length, and thus, there would
be no need to wrap the return type in a \\(\\text{Maybe}\\).

What if we wanted to concatenate two vectors? Such a function would need to
add their lengths:

{{< latex >}}
\text{nthElem} : \forall \alpha. \Pi n,m : \mathbb{N}. \text{Vec}\ \alpha \ n \rightarrow \text{Vec}\ \alpha\ m \rightarrow \text{Vec}\ \alpha\ (n+m)
{{< /latex >}}

Here we use our new type syntax for accepting two lengths \\(n\\) and \\(m\\), and defining
a function that, given two vectors, returns another vector whose length is the sum of the
first two's. We can't evaluate \\(n+m\\) (since we do not know the values of \\(n\\)
nor \\(m\\)), which should help convince us that our types, were we to add
this extension, should be able to support arbitrary expressions.

Alright, you might be thinking, this \\(\\Pi\\) thing seems useful enough. But do
we really have to add yet _another_ language construct, in addition to the regular
function arrow \\((\\rightarrow)\\)? Not so! In fact, the regular arrow is just
a special case of the product type, where the variable name \\(x\\) does not occur
in the return type. Notice that in this case, substitution does nothing at all, since
there's nothing to substitute! Thus, our above rule is simplified to:

{{< latex >}}
\frac
    {\Gamma\vdash e_1: \Pi x:\tau'. \tau \quad \Gamma\vdash e_2:\tau'}
    {\Gamma\vdash e_1\; e_2 : \tau}
{{< /latex >}}

And thus, we can see that \\(\\tau'\\rightarrow\\tau\\) is the same
as \\(\\Pi x : \\tau'. \\tau\\), if \\(x\\) does not occur in \\(\\tau\\).
That means that we can safely update the abstraction rule to produce
our \\(\\Pi\\)-types, too:

{{< latex >}}
\frac
    {\Gamma,x:\tau'\vdash e:\tau}
    {\Gamma\vdash \lambda x:\tau'. e : \Pi x : \tau'. \tau}
{{< /latex >}}

### Bringing it Together

Okay, now our application and abstraction rules look quit a bit like those
for their type-based counterparts. However, they're still not quite the same:
in the type application rule, we have to explicitly denote type application
as \\(e\\ [\\tau']\\), since types are not expressions. Furthermore,
our abtraction case contains only \\(\\alpha\\), and not
something in the form \\(x : \\tau'\\). However, why don't we take
a hint from our earlier extension of \\(\\Gamma\\)?
If we squint at it a little, \\(\\alpha\\ \\text{type}\\) starts to look like \\(\\alpha : \\text{Type}\\).
We could make this work, if we were to extend our type grammar with another object, \\(\\text{Type}\\),
which is the type of types (also known as a kind).
In this case, we'd be able to write \\(\\forall \\alpha. \\tau\\) as \\(\\Pi \\alpha:\\text{Type}. \\tau\\).
Our rule for \\(\\Lambda\\)-abstractions then starts to look like:

{{< latex >}}
\frac
    {\Gamma,\alpha : \text{Type}\vdash e:\tau}
    {\Gamma\vdash \Lambda \alpha : \text{Type}. e : \Pi \alpha : \text{Type}. \tau}
{{< /latex >}}

This is, however, identical to the rule for regular abstraction! We may as well
throw away the special \\(\\Lambda\\) syntax, and stick with only using
regular \\(\\lambda\\)s from now on. The last remaining detail is the special
type application \\(e\\ [\\tau']\\), which we have up till now distinguished
from regular applications. However, what if we didn't do that? What if types
could be treated like plain old expressions? Our rule for type application would
then look like:

{{< latex >}}
\frac
    {\Gamma\vdash e_1:\Pi \alpha : \text{Type}. \tau \quad \Gamma\vdash e_2 : \text{Type}}
    {\Gamma\vdash e_1\; e_2 : \tau[e_2/\alpha]}
{{< /latex >}}

To ensure the application is well-formed, we have to check that the argument \\(e_2\\),
which replaces the \\(\\tau\\) from the original rule, still represents a type.
With that change, this type application rule is once again just a special case of the regular
application rule that we defined earlier.

And now, a remark: observe that earlier, we wanted our types to contain expressions. We can
write this (informally) as \\(\\text{expr} \\subseteq \\text{type}\\). However, we just
decided that we'd allow types to appear in expressions, and thus, \\(\\text{type} \\subseteq \\text{expr}\\).
From this, it seems as though \\(\\text{type} = \\text{expr}\\), and indeed, this is true!
Expression and types are one and the same thing in Maypop and other dependently typed languages,
so the abstract syntax can be roughly written as:

{{< latex >}}
\begin{array}{lcll}
t \in \text{term} & ::= &\lambda x : t. t &\textit{(abstraction)}\\
 & | & t\  t & \textit{(application)} \\
 & | & x & \textit{(variable reference)} \\
 & | & \text{Type} & \textit{(type of types)} \\
 & | & \Pi x : t. t & \textit{(product type)}
\end{array}
{{< /latex >}}

This serves as the foundation for the Maypop language.
