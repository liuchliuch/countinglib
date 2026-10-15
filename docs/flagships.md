# Classification and representation results

The public entries preserve the hypotheses, output representations, and
reduction models of their original research results. Two Holant research lines
share one flagship import.

The [references page](references.md#research-papers-and-lean-sources) gives each paper's
arXiv link, original Lean GitHub release, and corresponding library entry.

| Entry | Mathematical scope | Complexity and representation |
| --- | --- | --- |
| `Counting.Flagships.Holant` | Full Boolean Holant dichotomy and binary-disequality variants, with finite algebraic-complex languages and explicit resource conditions | Fixed-language evaluation machines and the original witness-counting hardness reductions; full Holant and binary variants retain distinct exact output codecs |
| `Counting.Flagships.ComplexCSP` | Complex-weighted CSP structural collapse, fixed-language classification, positive-degree extensions, and effective recognition | Algebraic tables with positive arity; public collapse/recognition retains nonempty-domain assumptions. Fixed-field coordinate outputs and charged promised Turing reductions |
| `Counting.Flagships.PlanarHom` | Nonnegative symmetric algebraic-real interaction matrices on ordinary planar multigraphs, with unit or strictly positive algebraic-real vertex weights | Fixed-language bit machines and charged promised hardness; loops, parallel edges, and isolated vertices remain in the input model |
| `Counting.Flagships.MatchgateWidth` | Qutrit support trichotomy, width lower bounds, exact field-preserving realizations, and compression under the specified rank/deficiency/presentation premises | Representation and compression theorems; no generic bit-time evaluation guarantee is attached to the headline statements |

Concrete applications are available in the [Holant](examples/Holant.lean),
[ComplexCSP](examples/ComplexCSP.lean), [PlanarHom](examples/PlanarHom.lean), and
[Matchgate Width](examples/MatchgateWidth.lean) tutorials. They prove the stated
premises for explicit data before applying the corresponding public endpoint.

## Fixed data and runtime input

A fixed-language evaluator may depend on the language, represented number field,
and basis. Its polynomial bound is for encoded instances of that fixed problem.
A terminating recognizer with the language as input has a different contract;
the public recognition results do not assert uniform polynomial-time recognition.

Natural-valued #P membership and complex-weighted partition evaluation use
different output and reduction interfaces. General-graph hardness does not
supply planar hardness. A semantic compression or tensor identity does not alone
supply a machine reduction.

## Source versions

[data/upstream-lock.json](../data/upstream-lock.json) pins the research releases.
The source entries in the [reference](reference.md) lead to the original
statement structures and public wrappers.

The ComplexCSP recognition chain uses the corrected all-finite-instance version
of the isomorphism criterion associated with the original paper's Theorem 5.2.
The printed simple-instance formulation and its counterexample are recorded
separately; the corrected production result is not labeled as a proof of that
printed formulation.

The PlanarHom full-real appendix and preserved Holant modules outside the
flagship closure are outside the current selected acceptance. Read
[verification scope](verification.md) for the distinction between retained
sources and selected proof modules.
