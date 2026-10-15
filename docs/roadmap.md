# Roadmap

CountingLib's next stage focuses on adoption, public interfaces, and reusable
extensions. Existing complete research results and their integrated proof
closures remain the foundation of this work.

## Public release

The source repository, versioned Lake installation, English guides, and citation
index are available. Version 0.1.1 adds a searchable selected-API reference,
flagship tutorials, and continuous installation and profile checks.

- Extend the API reference when a new public interface is accepted.
- Add examples driven by concrete downstream uses.
- Calibrate broader CI profiles against their actual memory and storage needs.
- Clarify the remaining component-specific license decisions with rights holders.

Toolchain updates remain separate from mathematical changes and require fresh
compatibility verification.

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
