import ComplexCSP.Structure.MaltsevCSPWitness
import ComplexCSP.Structure.MaltsevTypeCost

/-! The actual finite witness constructor used by the positive classification proof.
This entry exposes satisfiability and operation counting, without a bit-time claim. -/
namespace Counting.ComplexCSP.Classification.Maltsev
open _root_.ComplexCSP.MaltsevWitness _root_.ComplexCSP.MaltsevRelations

/-- Construct a stored witness and inspect its seed; no solution oracle is an input. -/
def solve {d n : ℕ} (m : Operation (Fin d)) (defaultValue : Fin d)
    (constraints : List (FiniteConstraint d n)) : Bool :=
  (construct m defaultValue constraints).seed.isSome

theorem solve_correct {d n : ℕ} {m : Operation (Fin d)} (hm : IsMaltsev m)
    (defaultValue : Fin d) (constraints : List (FiniteConstraint d n))
    (preserved : TablesPreserved m constraints) :
    solve m defaultValue constraints = true ↔ ∃ x, Satisfies constraints x :=
  construct_seed_correct hm defaultValue constraints preserved

end Counting.ComplexCSP.Classification.Maltsev
