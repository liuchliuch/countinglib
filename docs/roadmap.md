# Roadmap

CountingLib's next stage focuses on adoption, public interfaces, and reusable
extensions. Existing complete research results and their integrated proof
closures remain the foundation of this work.

## Public release

- Publish a reproducible source repository with clear licensing and attribution.
- Maintain concise guides, compiled examples, and a searchable API reference.
- Test ordinary downstream Lake dependencies and automate relevant build profiles.
- Establish a version policy that separates dependency updates from mathematical changes.

## Reusable infrastructure

- Align general mathematical lemmas with mathlib and complexity foundations with CSLib.
- Extend representation transports when a second concrete consumer requires them.
- Add resource, degree, and planarity preservation to specific reduction interfaces.
- Refine variable-elimination costs to include the required structure and bit operations.
- Extend public frontends to machine encodings with explicit input ranges and costs.

## Further algorithms and theory

Counting/sampling equivalences, permanent algorithms, correlation decay,
zero-free approximation, certified hashing, and broader complexity-theory
results are demand-driven extensions. Each should have an independent input,
output, execution, cost/probability contract, and useful downstream client.

Contribution units should be small enough to review and independently validate.
See [contributing](../CONTRIBUTING.md) and [release preparation](release.md).
