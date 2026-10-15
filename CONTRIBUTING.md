# Contributing to CountingLib

Use the committed Lean version and dependency locks. Build from the repository
root through `./scripts/lake`; Python tools require Python 3.11 or later.

## Design an interface

Read the [architecture](docs/architecture.md) and [API guide](docs/api.md) first.
Reuse existing definitions and give each module one Lake provider. Keep semantic
models, executors, machine refinements, and classification endpoints separate.

State fixed parameters, runtime inputs, promises, output representations, and
cost models. Preserve occurrences, ordered/repeated ports, isolated variables,
zero/nullary factors, loops, and parallel edges within the claimed model.
Natural-valued #P membership and complex-weighted evaluation require distinct
contracts.

Include a meaningful client and boundary cases. Do not add `sorry`, `admit`, new
mathematical axioms, or assumptions that contain the desired conclusion.

## Validate a change

First build the affected module and client:

```sh
./scripts/lake build +Counting.Model.FiniteSums
./scripts/lake lean docs/examples/RelationalCounting.lean
```

Then run the relevant [verification profile](docs/verification.md) on stable
sources. Run one verifier at a time. Changes to shared providers or classification
imports may require a broader profile.

Documentation changes should pass:

```sh
python3 scripts/check_public_docs.py
```

Keep source commits, notices, and original contracts with imported results.
Archive earlier receipts instead of rewriting them. Describe semantic,
operation-count, encoded-runtime, and probability guarantees at their actual
proved strength.

## Submit a contribution

Keep a pull request focused on one interface or result. Explain the mathematical
change, affected imports, validation commands, and source attribution. Disclose
AI assistance and ensure a contributor can explain and maintain the submitted
proofs. Contributions to upstream libraries follow their own policies.

Resolve source licensing before including new material in a public release;
see [license scope](LICENSE.md).
