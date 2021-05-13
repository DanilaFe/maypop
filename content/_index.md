---
title: Maypop Home
description: Maypop is a dependently typed programming language implemented using Literate Haskell.
---
{{< todo >}}Everything! Maypop is an ongoing project; right now, we're still halfway through
the school term! At the time of writing, we have completed only a handful of our goals
for the language; stay tuned to see more!{{< /todo >}}

Hi, and weclome to Maypop! This site is a little bit of an experiment - we're implementing
a dependently typed language entirely using Literate Haskell. The idea is to guide users
through our code using a narrative, instead of just throwing a completed repository at them.
With that out of the way, feel free to look around the available modules!

If you want some guided reading, we suggest going first to [`Syntax`]({{< ref "modules/syntax.md" >}}),
then to [`Evaluation`]({{< ref "modules/eval.md" >}}), then to [`Checking`]({{< ref "modules/checking.md" >}}).
There are also examples of code in Maypop in [`Examples`]({{< ref "modules/examples.md" >}}), and some code
to test the type checker in [`Spec`]({{< ref "modules/spec.md" >}}). If you still have energy by
then, check out [`Modules`]({{< ref "modules/modules.md" >}}) for our module data structures,
[`Loading`]({{< ref "modules/loading.md" >}}) for how these modules are actually loaded from disk,
and [`LoadingImpl`]({{< ref "modules/loadingimpl.md" >}}) for the actual I/O implementation
of file loading. The [`Parser`]({{< ref "modules/parser.md" >}}) contains a parser for the language,
but it is not yet described; the parser is incomplete, and the current concrete syntax is very wonky.
Proceed at your own risk.
