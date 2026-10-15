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
| `.github/workflows/ci.yml` | Core verification and tutorial CI; broader profiles are manual |

Development history, internal reports, source working copies, project caches,
and generated large ledgers stay outside the publication tree. Historical
component prose is preserved in the development workspace; the public guides
and reference index provide the current English interface.

## Versions and dependencies

The initial source release is [v0.1.0](https://github.com/liuchliuch/countinglib/releases/tag/v0.1.0)
on the repository's `main` branch. Pin a tag or commit in downstream projects.
The toolchain remains Lean 4.34.1 with the committed mathlib and Lake locks.
Future toolchain updates require separate compatibility work and fresh acceptance.

## Verification policy

CI runs the core profile and public examples on pushes and pull requests. Manual
runs select `algorithms`, `reuse`, or `all`. Full profiles require a runner
provisioned for their larger closure. Record the exact source commit and actual
outcomes; an in-progress workflow is not a passing verification result.

Before a release, check source ownership, dependency locks, public documentation,
client compilation, declaration audits, and the supported installation path.
Retain original source notices and apply the [license scope](../LICENSE.md).
The [verification guide](verification.md) distinguishes accepted local evidence,
cold reconstruction, hosted CI, and independent kernel replay.
