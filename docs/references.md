# References

This page connects research papers, their original Lean formalizations, and
CountingLib's public entry points. GitHub links pin the source commits imported
into this library. Read the [classification contracts](flagships.md) for the
precise scope and the [API reference](reference.md) for local declarations.

## Research papers and Lean sources

| Research line | Paper | Original Lean release | CountingLib entry |
| --- | --- | --- | --- |
| Full Boolean Holant | Liu, Meng, and Wang (2026), [*A Full Complexity Dichotomy for Complex-Valued Boolean Holant Problems*](https://arxiv.org/abs/2610.00081v1) | [holant-dichotomy-lean · `97731bc`](https://github.com/liuchliuch/holant-dichotomy-lean/tree/97731bce1618bef0d9ee7911b6ac8bc8698077b2) | [Counting.Flagships.Holant](../Counting/Flagships/Holant.lean) |
| Binary-disequality Holant | Liu and Meng (2026), [*A Dichotomy for Complex Boolean Holant with Binary Disequality*](https://arxiv.org/abs/2609.00219v1) | [holant-binary-disequality-lean · `ec3e598`](https://github.com/liuchliuch/holant-binary-disequality-lean/tree/ec3e598e380c57e1c4d1a3c73a4ad1b4f7eed711) | [Counting.Flagships.Holant](../Counting/Flagships/Holant.lean) |
| Complex-weighted CSP | Liu and Meng (2026), [*From Block Orthogonality to Decidability in Complex-Weighted Counting CSP*](https://arxiv.org/abs/2608.14845v1) | [complex-csp-decidability-lean · `c454c2d`](https://github.com/liuchliuch/complex-csp-decidability-lean/tree/c454c2d6426cd8b9f9bcfd3e54bd69de1dcf48ec) | [Counting.Flagships.ComplexCSP](../Counting/Flagships/ComplexCSP.lean) |
| Nonnegative planar homomorphisms | Liu and Meng (2026), [*A Dichotomy for Planar Graph Homomorphisms with Nonnegative Weights*](https://arxiv.org/abs/2610.05412v1) | [planar-homomorphisms-lean · `db68e74`](https://github.com/liuchliuch/planar-homomorphisms-lean/tree/db68e745380769c38c8347736d2d84fcde38263c) | [Counting.Flagships.PlanarHom](../Counting/Flagships/PlanarHom.lean) |
| Matchgate Width | Liu and Meng (2026), [*When Matchgate Base Collapse Fails: A Qutrit Trichotomy and Unbounded Exact Width*](https://arxiv.org/abs/2610.00079v1) | [matchgate-width-lean · `da4f3a7`](https://github.com/liuchliuch/matchgate-width-lean/tree/da4f3a7beda4651a615638c361927820035e83d9) | [Counting.Flagships.MatchgateWidth](../Counting/Flagships/MatchgateWidth.lean) |

The arXiv links identify paper versions; the Lean links identify separate source
snapshots. Binary-disequality Holant's pinned repository contains a revised
manuscript and its correspondence notes. ComplexCSP uses the corrected
all-finite-instance isomorphism criterion described in
[classification scope](flagships.md#source-versions). PlanarHom's original
citation retains an [author-hosted manuscript](https://liuchliuch.github.io/files/dichotomy-planar-graph-homomorphisms-nonnegative-weights.pdf);
the arXiv record above supplements that preserved attribution.

## Selected foundations and algorithm literature

These sources provide background for the listed interfaces. Their inclusion is
not a claim that every result in each paper has been formalized. The
[algorithm contracts](algorithms.md) specify the actual guarantees.

| Source | Related interface |
| --- | --- |
| Valiant (1979), [*The Complexity of Enumeration and Reliability Problems*](https://doi.org/10.1137/0208032) | Natural-valued #P, counting reductions, and witness transport |
| Cai and Chen, [*Complexity of Counting CSP with Complex Weights*](https://arxiv.org/abs/1111.2384) | Complex-weighted CSP classification and its structural conditions |
| Fisher (1961), [*Statistical Mechanics of Dimers on a Plane Lattice*](https://doi.org/10.1103/PhysRev.124.1664) | Pfaffian and planar dimer background for FKT/Ising interfaces |
| Karp, Luby, and Madras (1989), [*Monte-Carlo Approximation Algorithms for Enumeration Problems*](https://doi.org/10.1016/0196-6774%2889%2990038-2) | #DNF approximation and probability guarantees |
| Valiant (2008), [*Holographic Algorithms*](https://doi.org/10.1137/070682575) | Basis transformations, partition invariance, and matchgate context |

## Lean infrastructure

- [Lean 4](https://github.com/leanprover/lean4): theorem prover and language;
  CountingLib pins `leanprover/lean4:v4.34.1`.
- [mathlib at the locked commit](https://github.com/leanprover-community/mathlib4/tree/d13f23b723b8a846827a245b89c10fc7d3f11612):
  shared mathematical and machine infrastructure.
- [Source lock](../data/upstream-lock.json) and [provenance](../PROVENANCE.md):
  complete imported repository identities and ownership records.

## Citation practice

Cite the relevant paper and identify the original Lean source commit when using
one of its results. The original releases contain `CITATION.cff` metadata.
Identify the CountingLib commit or release separately when using its public
bridges, algorithms, or assembled interfaces. The current source release is
[CountingLib v0.1.1](https://github.com/liuchliuch/countinglib/releases/tag/v0.1.1);
repository citation metadata is in [CITATION.cff](../CITATION.cff).
