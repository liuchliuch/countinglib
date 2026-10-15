# Getting started

Use a source checkout to explore the library, or add it as a dependency to your
own Lean project. Both require the pinned Lean version.

## Build a checkout

Install elan, Git, and Python 3.11 or later, then run:

```sh
git clone https://github.com/liuchliuch/countinglib.git
cd countinglib
./scripts/lake exe cache get
./scripts/lake build
```

Use `scripts/lake` for commands inside the checkout. It configures Lake's module
map and clears inherited Lean search paths. Existing matching dependency caches
can be reused; local library artifacts are built from the checkout.

Build an optional collection or a single entry point with:

```sh
./scripts/lake build CountingReuse
./scripts/lake build CountingAlgorithms
./scripts/lake build +Counting.Flagships.ComplexCSP
```

The default target is `Counting`. A target can compile more modules than a single
Lean import reaches; classification entry points remain optional.

## Add a dependency

Add the versioned release to your downstream `lakefile.toml`:

```toml
[[require]]
name = "countingComplexity"
git = "https://github.com/liuchliuch/countinglib"
rev = "v0.1.0"
```

For local development, replace `git` and `rev` with `path = "../countinglib"`
when the downstream project is next to the checkout.

Use the checkout's `lean-toolchain`, then run `lake update` and `lake build` **in
the downstream project**. Updating there resolves its new dependency;
leave CountingLib's committed dependency locks unchanged. On a host requiring a
fallback Git executable, put that executable on `PATH` first.

Pin a release tag or commit to keep builds reproducible. The Lake package name
is `countingComplexity`; Lean imports remain under `Counting`.

## Run the examples

From the CountingLib checkout:

```sh
./scripts/lake lean docs/examples/RelationalCounting.lean
./scripts/lake lean docs/examples/GraphReduction.lean
./scripts/lake lean docs/examples/Interpolation.lean
```

| Example | What it demonstrates |
| --- | --- |
| [Relational counting](examples/RelationalCounting.lean) | A repeated unary constraint fixes one Boolean variable; an isolated variable leaves two satisfying assignments. The partition equals the public witness count. |
| [Graph reduction](examples/GraphReduction.lean) | A loop, parallel edges, and an isolated vertex survive a natural-weight graph-to-CSP reduction. Both partitions are `5298`; the actual transformer takes `51` transitions on a source encoding of length `24`. |
| [Interpolation](examples/Interpolation.lean) | Three rational samples recover the coefficient `3` of `3X² + 2X + 5`. The measured execution uses three queries and eighteen field operations. Duplicate nodes are rejected. |

The examples import public interfaces rather than classification aggregates.
Their semantic equalities and machine or operation bounds are separate theorems.

## Choose a narrower import

Start with the [API guide](api.md). Use a component module when you only need its
semantics or arithmetic result; import its machine layer when you need an encoded
execution guarantee. `Counting.Library` loads the main aggregates and their
larger classification proof closures. Optional reuse machine and `All` layers
still require explicit imports.
