import Counting.GraphCSP.Encoding
import Counting.GraphCSP.Semantics
import Counting.GraphCSP.Structure
import Counting.GraphCSP.Machine
import Counting.Complexity.Reduction

/-!
# A concrete parsimonious reduction for fixed weighted graph evaluation

The source and target encodings are independently faithful. The instance map is
implemented by the finite scan/reverse TM2 and preserves values through the S1
partition theorem. Neither computability nor polynomial runtime is a premise.
-/

set_option backward.isDefEq.respectTransparency false

namespace Counting.GraphCSP

/-- The genuine finite-alphabet instance transformer. It does not inspect the
fixed interaction or weight tables. -/
noncomputable def graphTransformer :
    Counting.Computation.PolyTime graphEncoding cspEncoding Graph.toCSP :=
  Machine.mapPolyTime graphEncoding cspEncoding Graph.toCSP symbolMap
    (fun G => (encode_transform G).symm)

/-- The actual computer's time polynomial, in source symbols. -/
@[simp] theorem graphTransformer_time : graphTransformer.time =
    Polynomial.C 2 * Polynomial.X + Polynomial.C 3 := rfl

/-- Every input and every materialized output symbol is charged by the exact run. -/
@[simp] theorem graphTransformer_steps (G : Graph) :
    (graphTransformer.outputsFun G).steps = 2 * (graphEncode G).length + 3 := rfl

/-- The complete explicit graph size is charged to the chosen input length. -/
theorem graphSize_le_encoded_length (G : Graph) :
    G.n + G.edges.length ≤ (graphEncode G).length := by
  have h := records_length_le (G.toCSP.constraints.map Constraint.toRaw)
  have hl := encode_transform_length G
  simp only [List.length_map, Graph.toCSP_constraints_length] at h
  simp only [cspEncode, rawEncode, List.length_append, List.length_replicate,
    List.length_cons] at hl
  omega

/-- The same machine also transforms raw words, not only canonical encodings.
This exact run theorem includes malformed words; semantic correctness below is
restricted to the executable decoder's accepted words. -/
theorem graphTransformer_run (xs : List SourceSymbol) :
    (fun c : Option graphTransformer.tm.Cfg => c.bind graphTransformer.tm.step)^[
      2 * xs.length + 3]
      (some (Turing.initList graphTransformer.tm xs)) =
        some (Turing.haltList graphTransformer.tm (xs.map symbolMap)) := by
  dsimp only [graphTransformer, Machine.mapPolyTime]
  have hm : xs.flatMap (fun a => [symbolMap a]) = xs.map symbolMap := by
    induction xs with
    | nil => rfl
    | cons a xs ih => simp [ih]
  simpa only [hm, List.length_map, two_mul] using
    (Machine.flatMap_run (fun a => [symbolMap a]) xs)

/-- On every accepted source word the materialized target is accepted and
represents the value-preserving target instance, including noncanonical digits. -/
theorem graphTransformer_accepted_code (xs : List SourceSymbol) (G : Graph)
    (h : graphDecode xs = some G) :
    cspDecode (xs.map symbolMap) = some G.toCSP := decode_transform h

/-- A natural-valued graph evaluation reduces parsimoniously to evaluation of a
fixed two-label CSP language. No positivity or symmetry hypotheses are required. -/
noncomputable def graphToCSPReduction {D : Type} [Fintype D]
    (M : D → D → Nat) (w : D → Nat) :
    Counting.Complexity.ParsimoniousReduction graphEncoding cspEncoding
      (fun G => G.partition M w) (fun I => I.partition M w) where
  map := Graph.toCSP
  machine := graphTransformer
  correct G := (G.partition_toCSP M w).symm

@[simp] theorem graphToCSPReduction_map {D : Type} [Fintype D]
    (M : D → D → Nat) (w : D → Nat) (G : Graph) :
    (graphToCSPReduction M w).map G = G.toCSP := rfl

/-- The implemented reduction does not depend on the particular fixed tables. -/
@[simp] theorem graphToCSPReduction_machine {D : Type} [Fintype D]
    (M : D → D → Nat) (w : D → Nat) :
    (graphToCSPReduction M w).machine = graphTransformer := rfl

/-- Proposition-valued reducibility retains the genuine finite-machine witness. -/
theorem graphToCSP_reduces {D : Type} [Fintype D]
    (M : D → D → Nat) (w : D → Nat) :
    Counting.Complexity.ParsimoniousReduces graphEncoding cspEncoding
      (fun G => G.partition M w) (fun I => I.partition M w) :=
  ⟨graphToCSPReduction M w⟩

/-- Any genuine target evaluator can be composed with the instance transformer.
This is conditional transport of FP, not a claim that all such CSPs are easy. -/
theorem graphEvaluation_inFP {D Γ : Type} [Fintype D] [Fintype Γ]
    (M : D → D → Nat) (w : D → Nat) (en : Computability.Encoding Nat Γ)
    (h : Counting.Computation.InFP cspEncoding en (fun I => I.partition M w)) :
    Counting.Computation.InFP graphEncoding en (fun G => G.partition M w) :=
  (graphToCSPReduction M w).inFP h

end Counting.GraphCSP
