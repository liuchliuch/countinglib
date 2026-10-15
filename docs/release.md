# Release policy

The public repository is named **CountingLib** (`countinglib`). The current Lake
package remains `countingComplexity`, and Lean imports remain under `Counting`.
These names can differ without changing theorem identifiers.

## Publication layout

| Path | Contents |
| --- | --- |
| `README.md` | Project scope, build commands, public imports, and navigation |
| `docs/` | English architecture, usage, contracts, and executable examples |
| `Counting/` | Root public aggregates and integration bridges |
| `projects/` | Component production sources, configurations, validation inputs, notices, and provenance metadata |
| `scripts/`, `tests/`, `validation/` | Fresh-build verification tools and their fixtures |
| `data/` | Fixed source inventory and public declaration metadata |
| `.github/workflows/ci.yml` | Core CI, scheduled extended profiles, and an optional full gate |

Development history, internal reports, source working copies, project caches,
and generated large ledgers stay outside the publication tree. Historical
component prose is preserved in the development workspace; the public guides
and reference index provide the current English interface.

## Versions and dependencies

The current release is [v0.1.1](https://github.com/liuchliuch/countinglib/releases/tag/v0.1.1)
on the repository's `main` branch. The initial v0.1.0 tag remains available. Pin a tag or commit in downstream projects.
The toolchain remains Lean 4.34.1 with the committed mathlib and Lake locks.
Future toolchain updates require separate compatibility work and fresh acceptance.

## Verification policy

CI checks the core, fresh introductory tutorials, and an actual downstream Git
installation on pushes and pull requests. Algorithms and reusable tools run
weekly or on manual request. Full release verification runs serially on a
suitable local host or explicitly configured dedicated runner. The
[CI guide](continuous-integration.md) specifies triggers, resources, retained
evidence, and Pages deployment.

The release gate requires all four profiles, fresh compilation and declaration
auditing of seven tutorials, and installation from the exact public Git commit.
Only a `release-ready` result and passed corresponding hosted core CI support
creating the release tag.
Before a release, check source ownership, dependency locks, public documentation,
client compilation, declaration audits, and the supported installation path.
Retain original source notices and apply the [license scope](../LICENSE.md).
The [verification guide](verification.md) distinguishes accepted local evidence,
cold reconstruction, hosted CI, and independent kernel replay.
