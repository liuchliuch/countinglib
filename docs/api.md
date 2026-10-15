# API guide

Choose an interface by the mathematical task, then import the smallest module
that provides its required execution contract. Lean declarations specify the
complete hypotheses; source links and extracted types are in the [reference](reference.md).

## Counting and reductions

| Task | Import | Representative interface |
| --- | --- | --- |
| Count accepted elements of a finite type | `Counting.Foundation.Witness` | `countAccepted`, `countAccepted_equiv`, `countAccepted_product` |
| Count fixed-length Boolean witnesses | `Counting.Foundation.Witness` | `witnessCount`, `witnessCount_falsePadding` |
| Encode values and compose real machines | `Counting.Encoding.Basic`, `Counting.Computation.PolyTime` | Codecs, round trips, `PolyTime.comp`, encoded output bounds |
| Define natural-valued #P membership | `Counting.Complexity.SharpP` | `SharpPWitness`, `InSharpP` |
| Construct a count-preserving reduction | `Counting.Complexity.Reduction` | `ParsimoniousReduction`, `trans`, `HardFor.transport` |
| Transport #P membership down a reduction | `Counting.SharpPClosure` | `ParsimoniousReduction.sharpPWitness`, `inSharpP` |
| Relate witness and accepting-path models | `Counting.Bridge.WitnessSharpP` | `bits_inSharpP_iff_acceptingPaths` |
| Reduce to independent counting NOR instances | `Counting.CookLevin` | `target_inSharpP`, `machineReduction`, `sharpP_reduces` |
| Compile a charged one-query reduction | `Counting.Reduction.OneQuery` | `compile`, `chain`, `substitute` |

Witness transport and the public accepting-path equivalence use standard binary
inputs. Unique false padding preserves the count; unrestricted ignored bits
multiply it. Codec round trips alone do not supply a polynomial-time converter.

## Weighted models

| Task | Import | Representative interface |
| --- | --- | --- |
| Define signatures and open instances | `Counting.Model.Basic` | `Language`, `Occurrence`, `OpenInstance.partition` |
| Split and relabel assignment sums | `Counting.Model.FiniteSums`, `Counting.Model.Relabel` | Assignment equivalences and partial sums |
| Glue instances or substitute gadgets | `Counting.Gadget.Composition` | `partition_glue`, `partition_disjointUnion`, substitution `partition_compile` |
| Interpret multigraphs as weighted constraints | `Counting.Model.Graph` | `MultiGraph.toOpenInstance`, `partition_toOpenInstance` |
| Count satisfying assignments through partition semantics | `Counting.Integration.RelationalCounting` | `RelationLanguage.partition_eq_countAccepted`, `partition_eq_witnessCount` |
| Execute the natural-weight graph-to-CSP reduction | `Counting.GraphCSP.Reduction` | `graphToCSPReduction`, `graphTransformer_steps` |

Model bridges preserve the representation's occurrence multiplicities and port
order. A value identity supplies the semantic part of a reduction; encoding and
machine obligations remain explicit.

## Intermediate tools

| Tool | Ordinary import | Optional layers |
| --- | --- | --- |
| Paired-stub open networks | `Counting.Bridge.OpenNetwork` | `.Corrected`, `.Canonical`, `.Composition`, `.Ordinary` |
| Exact fixed-gadget elimination | `Counting.Reduction.FixedGadget` | `.Machine`, `.Extension`, `.S1`, `.ExactField` |
| Fixed-field arithmetic | `Counting.Algorithm.FieldArithmetic` | `.Heights`, `.Materialized` |
| Parsimonious #P closure | `Counting.SharpPClosure` | `.Basic`, `.Machines`, `.Transport` |
| Product factor frontend | `Counting.Algorithm.ProductFinitePalette.Input` | `.Machine`, `.Clients` |

Open-network `raw` and corrected `tensor` have separate partition bridges;
composition is proved for all boundary assignments. Fixed-gadget machines use
their original graph codec and exact templates. The Product machine bridge uses
a fixed finite palette of factor inputs. Neither interface supplies a general
CSP-to-network serializer. Field arithmetic keeps a fixed field and basis,
including the original total division semantics `x / 0 = 0`.

## Algorithms and classification

The [algorithm guide](algorithms.md) lists public algorithm imports and their
cost models. The [classification guide](flagships.md) specifies fixed languages,
input promises, resources, and output representations. Import the individual
`Counting.Flagships.*` module for a classification result, or
`Counting.Library` for the main aggregates and selected machine adapters.
Optional reuse machine and `All` layers require explicit imports.
