# API browser

The [searchable API browser](https://liuchliuch.github.io/countinglib/docs/api.html) presents
333 selected declarations from 80 provider modules. It covers foundations and
algorithms, intermediate tools, and the Holant, ComplexCSP, PlanarHom, and
Matchgate Width flagship interfaces. Thirty contract families record their scope.
It is a curated entry point, not a complete declaration dump.

## Find and read an interface

Search declaration names, public export aliases, provider and import modules, or
any text in the full elaborated Lean types. Multiple words must all match.
Filter by collection, contract family, provider module, or declaration kind.
The `/` key focuses search. Search and filter state is preserved in the URL.

Each record supplies its import, canonical provider, source location, readable
Lean type, complete elaborated type, and scope and cost contract. Export aliases are identified as
alternate spellings of a single kernel declaration. Flagship records also link
the associated paper and pinned original Lean source, retaining manuscript
version qualifications. Declaration permalinks open the relevant readable type.

The readable view uses Lean's ordinary pretty printer, which may elide implicit
arguments or proof terms. The separate full `pp.all` view retains explicit detail. Some types are
large; the browser loads their display on demand and offers copying and an
expanded view. Recorded specification bodies are available separately.
Read the contract's promises and representation assumptions before using a
complexity conclusion. The browser renders existing environment exports; it
does not replace elaboration or proof and axiom verification.

## Build and preview

From the repository root, using Python 3.11 or later:

```sh
python3 scripts/build_api_site.py
python3 scripts/build_api_site.py --check
python3 -m unittest discover -s tests -p 'test_api_site.py'
python3 -m http.server 8000 --directory docs/api
```

Open `http://localhost:8000`. The generated directory is a self-contained static
site with no external JavaScript or CSS dependencies. Serve it over HTTP;
opening `index.html` as a local file may prevent the browser from loading its
JSON catalog.

The generator uses `projects/reuse-catalog/data/tool-index.json` and
`projects/reuse-contracts/data/flagship-index.json`, and `data/api/core-index.json`,
their corresponding full Lean type exports, and each declaration's source file.
`data/api/readable-types.jsonl` supplies readable versions of the original tool
and flagship types, bound to identical Lean expression data. It checks agreement with
the exported types, actual expression data, source hashes, and pinned Lean
toolchain before producing deterministic assets.
`--check` fails if generated files are absent, stale, or unexpected. Source-link
versions are configurable with `--version`; the default is `v0.1.1`.
The build manifest records input and output hashes.

The Pages workflow uploads only `docs/api` through GitHub Actions. Source and
prose-document links point to the configured repository release.
