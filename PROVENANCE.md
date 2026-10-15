# Source provenance

CountingLib combines original research formalizations, reusable bridges, and
new public interfaces on one pinned toolchain. Original theorem assumptions,
representations, algorithm contracts, and attribution remain with their sources.

## Research sources

[data/upstream-lock.json](data/upstream-lock.json) records eighteen research
repositories at fixed commits. Registration in that inventory does not imply
that every repository has been imported into the library.

[References](docs/references.md) pairs the research papers with their pinned Lean
GitHub sources and public library entries.

| Research line | Fixed source commit | Main provider |
| --- | --- | --- |
| Full Boolean Holant | `97731bce1618bef0d9ee7911b6ac8bc8698077b2` | `projects/holant-unified` |
| Binary-disequality Holant | `ec3e598e380c57e1c4d1a3c73a4ad1b4f7eed711` | `projects/holant-unified` |
| ComplexCSP | `c454c2d6426cd8b9f9bcfd3e54bd69de1dcf48ec` | `projects/complex-csp`, `projects/complex-csp-classification` |
| Nonnegative PlanarHom | `db68e745380769c38c8347736d2d84fcde38263c` | Canonical PlanarHom machine/algorithm providers and `projects/planar-classification` |
| Matchgate Width | `da4f3a7beda4651a615638c361927820035e83d9` | `projects/matchgate-width` |

Public model bridges and machine refinements are distinct from the original
classification proofs. The [reference](docs/reference.md) locates their actual
providers and extracted declaration types.

## Shared sources

`holant-core` provides six shared original Holant modules. `tractable-core`
provides eighteen canonical Product/Affine modules; legacy paths are aliases.
Other shared PlanarHom sources also have one canonical provider. Exact ownership
and selected-source inventories are produced by the root verifier.

Lean 4.34.1 and the nine Git dependencies are locked by the toolchain and Lake
manifests. Compatibility migration, newly proved bridges, and source registration
are separate records.

## Licensing

Original Holant releases and several algorithm components carry Apache-2.0
licenses; their LICENSE/NOTICE files are retained. The recorded PlanarHom and
ComplexCSP source releases have no specified software license. Some new interfaces
also need an explicit licensing decision.

No single license is assigned to the assembled repository. Publication makes
no additional reuse grant for components without an applicable license.
[LICENSE.md](LICENSE.md) records the file-specific scope and
[release policy](docs/release.md) describes versioning and verification.
