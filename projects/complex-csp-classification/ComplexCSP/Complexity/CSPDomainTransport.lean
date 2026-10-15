import ComplexCSP.Complexity.CSPColorRelabeling
import ComplexCSP.Complexity.GadgetSubstitutionReduction
import PlanarHom.PromisedFPReductionClosure

/-! # Exact ordinary and degree-promised FP transport across finite color names

Colors never occur in raw instance words. Relabeling preserves both the literal
partition word and the actual degree promise, so the same finite-control machine
serves either domain. These are transport theorems, not classification premises.
-/
namespace ComplexCSP.ComplexityCSPDomainTransport
open PlanarHom PlanarHom.Complexity ComplexityCSPCode
open ComplexityCSPColorRelabeling ComplexityGadgetSubstitution
variable {D E K : Type} [Fintype D] [Fintype E] [Field K] [Algebra ℚ K]
variable {s dimension : ℕ} (L : Language D K (Fin s)) (e : E ≃ D)
variable (basis : Module.Basis (Fin dimension) ℚ K)

omit [Fintype D] [Fintype E] [Field K] [Algebra ℚ K] in
theorem degreeValid_reindex (δ : ℕ) (g : Code) :
    DegreeValid (reindex L e) δ g ↔ DegreeValid L δ g := by
  have ho (hg : Valid L g) :
      (toInstance (reindex L e) g hg).occurrences=(toInstance L g hg).occurrences := by
    simp only [Instance.occurrences,toInstance,List.flatMap_map]
    rfl
  constructor <;> rintro ⟨hg,hd⟩ <;> refine ⟨hg,?_⟩
  · intro v
    have hh := hd v
    simpa only [Instance.occurrenceDegree,ho hg] using hh
  · intro v
    have hh := hd v
    simpa only [Instance.occurrenceDegree,ho hg] using hh

theorem degreePartitionProblem_reindex (δ : ℕ) :
    degreePartitionProblem (reindex L e) basis δ=degreePartitionProblem L basis δ := by
  have he : partition (reindex L e)=partition L := funext (partition_reindex L e)
  unfold degreePartitionProblem
  simp only [he,degreeValid_reindex]

/-- Reuse the exact promised bit machine under equality of its entire problem. -/
theorem inFP_reindex_iff :
    (ComplexityCSPCountReduction.partitionProblem (reindex L e) basis).InFP ↔
      (ComplexityCSPCountReduction.partitionProblem L basis).InFP := by
  rw [partitionProblem_reindex]

theorem degree_inFP_reindex_iff (δ : ℕ) :
    (degreePartitionProblem (reindex L e) basis δ).InFP ↔
      (degreePartitionProblem L basis δ).InFP := by
  rw [degreePartitionProblem_reindex]

/-- When an all-Code evaluator is available, its stronger total typed FP claim
also transfers, including the explicit unit defaults on malformed constraints. -/
theorem fp_partition_reindex_iff :
    FP encoding (numberFieldEncoding basis) (partition (reindex L e)) ↔
      FP encoding (numberFieldEncoding basis) (partition L) := by
  have he : partition (reindex L e)=partition L := funext (partition_reindex L e)
  rw [he]

/-- Canonical finite-color specialization in the direction used by the final
positive theorem; no computation on assignments is inserted in the machine. -/
theorem inFP_of_fin (h : (ComplexityCSPCountReduction.partitionProblem
    (reindex L (Fintype.equivFin D).symm) basis).InFP) :
    (ComplexityCSPCountReduction.partitionProblem L basis).InFP :=
  (inFP_reindex_iff L (Fintype.equivFin D).symm basis).mp h

theorem degree_inFP_of_fin (δ : ℕ) (h : (degreePartitionProblem
    (reindex L (Fintype.equivFin D).symm) basis δ).InFP) :
    (degreePartitionProblem L basis δ).InFP :=
  (degree_inFP_reindex_iff L (Fintype.equivFin D).symm basis δ).mp h

end ComplexCSP.ComplexityCSPDomainTransport
