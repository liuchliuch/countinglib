# CountingLib

**Counting complexity in Lean.**

[Website](https://liuchliuch.github.io/countinglib/) ·
[Documentation](https://liuchliuch.github.io/countinglib/docs/) ·
[API reference](https://liuchliuch.github.io/countinglib/docs/api.html) ·
[Examples](https://liuchliuch.github.io/countinglib/docs/examples.html) ·
[Papers and sources](https://liuchliuch.github.io/countinglib/docs/references.html)

CountingLib provides reusable counting semantics, reductions, algorithms, and
classification theorems. Its foundations connect finite witness counting to
concrete polynomial-time machines. Weighted CSP, Holant, and graph homomorphism
models share partition-function semantics while retaining their own input and
output representations.

The library includes Boolean Holant dichotomies, complex-weighted CSP
classification and effective recognition, nonnegative planar graph homomorphism
dichotomies, and matchgate-width results.

## Build

Install [elan](https://github.com/leanprover/elan), Git, and Python 3.11 or later.
From a source checkout:

```sh
git clone https://github.com/liuchliuch/countinglib.git
cd countinglib
./scripts/lake exe cache get
./scripts/lake build
```

The checkout pins **Lean 4.34.1** and mathlib commit
`d13f23b723b8a846827a245b89c10fc7d3f11612`. `cache get` retrieves matching
external dependency artifacts; `lake build` builds the default `Counting` target.

## Use

```lean
import Counting

open Counting.Foundation

example {A B : Type} [Fintype A] [Fintype B]
    (p : A → Bool) (q : B → Bool) :
    countAccepted (fun x : A × B => p x.1 && q x.2) =
      countAccepted p * countAccepted q :=
  countAccepted_product p q
```

Select an entry point for the result you need:

| Import | Contents |
| --- | --- |
| `Counting` | Counting foundations, encodings, machines, partition semantics, graph-to-CSP reduction, and interpolation |
| `Counting.Reuse` | Open-network bridges, fixed-gadget interfaces, field arithmetic, #P closure, and a Product input frontend |
| `Counting.Algorithms` | Exact and approximate algorithms, with their stated execution and cost contracts |
| `Counting.Flagships.Holant` | Full Boolean and binary-disequality Holant results |
| `Counting.Flagships.ComplexCSP` | Fixed-language classification, structural collapse, and effective recognition |
| `Counting.Flagships.PlanarHom` | Nonnegative algebraic planar graph homomorphism dichotomies |
| `Counting.Flagships.MatchgateWidth` | Width bounds, qutrit trichotomy, and exact compression |
| `Counting.Library` | Core, algorithm, reuse, and flagship aggregates with selected machine adapters |

The [getting started guide](docs/getting-started.md) covers downstream installation
and seven runnable examples. The Lake package name remains `countingComplexity`;
the public Lean namespace is `Counting`.

## Read

- [Architecture](docs/architecture.md): layers, ownership, and import choices.
- [API guide](docs/api.md): common tasks and their public interfaces.
- [Algorithms](docs/algorithms.md): input, correctness, and cost contracts.
- [Classification results](docs/flagships.md): precise mathematical scope.
- [Verification](docs/verification.md): builds, declaration audits, and recorded acceptance.
- [References](docs/references.md): papers, pinned original Lean repositories, and library entry points.
- [API browser](docs/api-site.md): search, complete types, and static reference generation.
- [API reference](docs/reference.md): source entry points and extracted Lean types.
- [Continuous integration](docs/continuous-integration.md): checks, resources, and release gates.
- [Contributing](CONTRIBUTING.md), [roadmap](docs/roadmap.md), and [source provenance](PROVENANCE.md).

## License

Source components retain their original licenses and attribution. CountingLib
has no blanket repository-wide license; see [license scope](LICENSE.md).
[Release policy](docs/release.md) records versioning and verification expectations.
