Using the std++ library
=======================
The first Coq version of this project is not finished. At some point the number
of required side lemmas became too much of a burden. The most interesting part
to verify is the Schreier-Sims algorithm, since this provides the subgroup chain
that is key to subsequent computational results. An initial goal would be to
formally prove Rubik's cube indeed has *43252003274489856000* possible
configurations.

I gained some experience using the std++ Coq library, and I think it can be used
to greatly simplify the proof burden for this project. The `fmap` (finite map)
type could be replaced with `Pmap` from std++. Introducing this change in-place
is too difficult, so I will have to start from scratch.
