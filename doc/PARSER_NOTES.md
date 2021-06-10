* Notes on Indentation Sensitivity

While working on Maypop, one feature we wanted to incorporate was indentation sensitivity, rather than relying on seperation characters, such as in our case `|` in our data type declarations and case expressions. While we knew this undertaking would be non-trivial, we did not anticipate the problems that presented themselves.

The first issue encountered, which eventually resolved itself, was the understanding that `GenTokenParser` would be incompatible with `IndentParserT`. While in the end this was found to be incorrect, it still presented a problem for a time. In the end, the solution was to replace instances of `Identity` in parser types with `IndentT Identity`, as this enabled indentation sensitivity, and is in line with the usage outlined in the documention for the `Indents` package.

The second, and more pressing issue we encountered were seemingly ambiguous cases introduced by the indentation sensitivity. In particular, in the file `Bool.mp`, when attempting to eliminate usage of `|` for data type declarations, we had several classes of problems arise.

The first of these is what we believe to be the parser incorrectly missing the first colon. For instance, rather than parsing `True : Bool` as a complete statement, it would parse `True : Bool (False)`. While the parsing could be considered "correct", upon type checking or completion of parsing we would encounter obvious errors.

The second case is incorrect identification of whitespace, which itself manifested in multiple ways. The situation that really exemplified the point was one where the parser did not detect the correct indentation level, expecting 2 levels, but when 2 levels of indentation are provided, the parser raises an error stating it expected no indentation. Upon removal of all indentation, an error is raised stating that there should be indentation. A catch .22.

The final case that arose was one in which the parser recognized alphanumeric characters as indentation. Namely, in the file `Bool.mp`, on line 5, it recognized `    False :` as 10 indentation characters, while one can see that only 4 exist. The source of this issue is unknown, nor is any documentation of such an issue existing in other code bases.

While being unable to resolve issues with indentation sensitivity is disappointing, it's worth noting that any indentation libraries focused around Parsec that we could find were severly lacking in documentation and examples. `Indents`, which we found to be the best one, had almost nothing in the way of documentation on such matters, only having 3 functions, `withBlock`, `withBlock'`, and `block`, none of which resolved our issue. Even explicit termination of parser chains on newlines didn't fix the issue, as many of our parsers we used from Parsec consume whitespace themselves.

Worth noting as well is line folding. Line folding is a very nice behavior to have, and one that would be wonderful to implement with indentation parsing, however, when using the line folding combinator, the issues presented by `Indents` were much more arcane, such as the incorrect parsing of non-whitespace characters as whitespace. Were there more time, using the line fold combinators as well as spending more time looking into the indentation sensitivity would be ideal.
