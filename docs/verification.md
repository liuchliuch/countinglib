# Verification

The verifier builds selected source closures, compiles clients, and audits actual
Lean declarations with private visibility. It includes generated declarations,
source ownership, compiled imports, fixed dependency state, and transitive axioms.

## Run a profile

```sh
python3 scripts/verify.py --scope core --workers 2
python3 scripts/verify.py --scope algorithms --workers 2
python3 scripts/verify.py --scope reuse --workers 2
python3 scripts/verify.py --scope all --workers 2
```

Run these serially on a stable source tree. `core` is the default. `reuse`
checks the intermediate-tool entries and their actual dependencies;
`all` includes classification and optional machine adapters. Results are written
to `validation/<scope>/result.json`; previous runs are archived before replacement.

`--inventory-only` writes a separate source inventory without proof acceptance.
`python3 scripts/verify.py --self-test --workers 2` checks the audit harness and
its rejection fixtures. A failed or interrupted run retains its recorded state.

## Accepted snapshot

The 2026-10-15 local snapshot has the following accepted profiles:

| Profile | Selected modules | Kernel declarations | Theorems |
| --- | ---: | ---: | ---: |
| core | 346 | 14,314 | 8,808 |
| algorithms | 2,099 | 66,132 | 41,954 |
| reuse | 1,861 | 59,832 | 37,797 |
| all | 12,533 | 605,425 | 424,017 |

Profiles overlap and must not be added. Theorem counts include generated
statements. The complete audit includes 38,288 private declarations, no unsafe
declarations, no new mathematical axioms, and no disallowed dependencies. Its
allowed foundational axioms are `propext`, `Classical.choice`, and `Quot.sound`.
Existing compiler recursion helpers are recorded separately from machine
termination and cost theorems.

The workspace owns 13,459 production modules. The 926 preserved Holant modules
outside the selected closure remain explicitly excluded. The public core,
algorithm, and reuse import closures contain 37, 1,414, and 311 local modules;
these are separate metrics from profile and Lake target sizes.

## Reproduce from source

A clean checkout contains no project build artifacts. Lake may retrieve matching
external dependency caches, then compile the selected local sources. The prior
isolated source validation rebuilt the core and the complete OpenNetwork entry
with independent clients. The final source handoff matched all owned sources,
129 harness/configuration inputs, and nine dependency locks to that tested tree.

The full local audit was accepted after an interrupted outer driver: its
underlying build completed, then the complete verifier ran on unchanged sources
with actual successful exit codes. This is a recovered incremental verification,
not a second cold build.

The publication candidate preserves these proof inputs and includes compact
historical results. Large audit ledgers and development history are regenerated
by a new verifier run; the candidate does not contain the complete old evidence
chain. A source build and axiom audit are distinct from an independent kernel
replay or a paper-to-statement correspondence review.

## Tutorials and continuous checks

`python3 scripts/check_examples.py --scope all --workers 2` builds the required
entry modules, compiles seven tutorials into fresh artifacts, and audits all of
their private/generated declarations and transitive axioms. Use `--scope core`
for the three introductory tutorials. This client audit is separate from the
production profile counts above.

The [CI guide](continuous-integration.md) describes exact-commit downstream
installation, scheduled profiles, resource limits, and the serial release gate.
Matching incremental caches may be used; any private cache preparation is
recorded separately and does not establish a new cold build.
