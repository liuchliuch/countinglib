# Continuous integration

CountingLib separates routine feedback from full release verification. Every run
uses the committed Lean 4.34.1 toolchain and Lake locks. Actions are pinned to
reviewed commits; no workflow upgrades the toolchain or creates a release tag.

| Trigger | Checks | Resources |
| --- | --- | --- |
| Push to `main`, pull request, manual `core` | Documentation and generated API, regressions and real Lean rejection fixtures, core source/declaration audit, three fresh tutorial clients, exact Git-SHA downstream installation | Standard public Ubuntu runner; two Lean workers |
| Weekly on Monday at 02:17 UTC, manual `algorithms` or `reuse` | Algorithm and reusable-tool profiles, each with source builds and private/generated declaration and transitive-axiom audits | Separate Ubuntu jobs, serialized; two workers |
| Manual `all` on `main` | Serial full release gate, including all four profiles, seven fresh tutorial clients and downstream installation | Explicitly configured dedicated runner |
| API changes on `main`, manual API deployment | Recheck generated site and deploy only `docs/api/` | Standard Ubuntu runner; no Lean build |

The Git dependency test generates an ordinary downstream `lakefile.toml` with
`git = "https://github.com/liuchliuch/countinglib"` and the exact tested commit as
`rev`. It checks that all local components remain inside that Git checkout and
that inherited external Git locks match. README clients and tutorial sources are
copied from the resolved checkout, then compiled into fresh consumer artifacts.
Pull-request tests use the tested merge SHA from the base repository.

## Caches and evidence

Hosted jobs restore caches keyed by operating system, architecture, toolchain,
locks, profile and commit, with a same-lock incremental fallback. Each verifier
still checks source/configuration stability, compiled inputs, declarations and
transitive axioms. Cache restoration is not evidence of a new cold build.

The downstream test explicitly shares matching external dependency checkouts
and copies matching library build artifacts into its isolated Git checkout.
It always creates new client sources and outputs. The receipt records every
cache source and command; it makes no claim that the entire library was rebuilt
without artifacts.

Passing and failed profile receipts and logs are retained as workflow artifacts
for 30 days. The full declaration ledgers accompany profile artifacts; artifacts
are diagnostics, not a separate independent kernel replay. Previous local
verification results are archived before replacement.

GitHub currently documents standard public Ubuntu runners as four CPUs and
16 GB RAM. The workflow removes unused preinstalled SDKs to make space for
matching mathlib artifacts. Extended hosted profiles remain subject to actual
runner capacity and the six-hour execution limit. A timed-out or failed run is
not accepted as verification; inspect its logs and run that exact commit on a
suitable host. The complete flagship closure is not assigned to that runner.

## Full release gate

The established local verification host has 128 GiB RAM. The gate conservatively
requires at least 64 GiB physical memory and 32 GiB free disk; these are resource
checks, not a measured minimum specification for every cold build.

After committing the release inputs, run on a stable checkout:

```sh
python3 scripts/check_release.py --commit COMMIT_SHA \
  --output .cache/release-checks-v0.1.1 --workers 2
```

Replace `COMMIT_SHA` with the full commit to publish. The commit must already be
fetchable from the public repository for the Git installation check. Use
`--source-only` for an earlier source preflight; its result explicitly remains
`source-checks-passed-awaiting-downstream`, rather than `release-ready`.
The complete gate runs `core`, `algorithms`, `reuse`, and `all` serially, freshly
compiles and audits all seven tutorials, then builds a fresh downstream project
from that exact Git SHA. A new output directory is required for every attempt.
Create the version tag only after the exact commit reaches `release-ready` and
the corresponding hosted core CI passes. Preserve those receipts with the
release evidence.

The same gate can run manually through CI after the owner sets the repository
variable `COUNTINGLIB_FULL_RUNNER` to JSON runner labels, for example
`["self-hosted", "countinglib-full"]`, and provisions a dedicated runner with
those resources. This optional path accepts trusted `main` only and is never
triggered by pull requests. Without that configuration, requesting `all` fails
with an explicit explanation; it cannot silently pass by skipping the job.
No runner registration, paid resources or credentials are needed for the local
release path.

## API Pages

Set the repository's Pages source to **GitHub Actions** once. The Pages workflow
checks `python3 scripts/build_api_site.py --check`, uploads only the generated
static `docs/api/` directory and deploys it to the `github-pages` environment.
Its write permissions are limited to Pages deployment and OIDC; verification
jobs use read-only repository access. Repository sources, caches and private
compiler artifacts are not part of the published site.

Sources: [GitHub runner resources](https://docs.github.com/en/actions/reference/runners/github-hosted-runners),
[workflow artifacts](https://docs.github.com/en/actions/tutorials/store-and-share-data),
[Lean action](https://github.com/leanprover/lean-action),
[Pages artifact requirements](https://github.com/actions/upload-pages-artifact).
