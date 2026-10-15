# Reference

[Search the public API](https://liuchliuch.github.io/countinglib/) by declaration,
module, or full Lean type. The generated reference covers selected public tool
and flagship declarations; it does not enumerate every internal proof.

Use Lean's `#check` and editor navigation after importing the corresponding
public module. The sources below contain the precise hypotheses and theorem
statements.

The separate [references page](references.md) connects arXiv papers and original Lean
GitHub releases to these public interfaces.

## Source entries

| Interface | Source |
| --- | --- |
| Finite witness counts | [Foundation.Witness](../projects/foundations/Counting/Foundation/Witness.lean) |
| #P witnesses | [Complexity.SharpP](../projects/foundations/Counting/Complexity/SharpP.lean) |
| Parsimonious reductions | [Complexity.Reduction](../projects/foundations/Counting/Complexity/Reduction.lean) |
| Weighted open instances | [Model.Basic](../projects/partition-semantics/Counting/Model/Basic.lean) |
| Instance and gadget composition | [Gadget.Composition](../projects/partition-semantics/Counting/Gadget/Composition.lean) |
| Relational partition counting | [RelationalCounting](../Counting/Integration/RelationalCounting.lean) |
| Exact graph-to-CSP transformation | [GraphCSP.Reduction](../projects/graph-csp-reduction/Counting/GraphCSP/Reduction.lean) |
| Measured interpolation | [Interpolation.Cost](../projects/interpolation/Counting/Algorithm/Interpolation/Cost.lean) |
| Holant endpoints | [Flagships.Holant](../Counting/Flagships/Holant.lean) |
| ComplexCSP endpoints | [Flagships.ComplexCSP](../Counting/Flagships/ComplexCSP.lean) |
| PlanarHom endpoints | [Flagships.PlanarHom](../Counting/Flagships/PlanarHom.lean) |
| Matchgate Width endpoints | [Flagships.MatchgateWidth](../Counting/Flagships/MatchgateWidth.lean) |

## Extracted declarations

The intermediate-tool catalog contains 184 extracted full types and 17
specification bodies. The flagship catalog contains 66 full types and 17
specification bodies. These are selected API records, not a full declaration
dump or an independent proof certificate.

- [Tool index](../projects/reuse-catalog/data/tool-index.json) and
  [full tool types](../projects/reuse-catalog/data/exported-types.jsonl).
- [Actual entry dependencies](../projects/reuse-catalog/data/entry-dependencies.json).
- [Flagship index](../projects/reuse-contracts/data/flagship-index.json) and
  [full flagship types](../projects/reuse-contracts/data/exported-types.jsonl).
- [Canonical provider relocation](../projects/reuse-catalog/data/provider-relocation.json).

The [API guide](api.md) is the concise navigation layer. For a result's scope,
read its full Lean type together with any named statement structure and codec.
