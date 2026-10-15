import ComplexCSP.Structure.SupportMaltsevBridge
import ComplexCSP.Structure.BlockOrthogonality

/-! # The original-table BO support bridge

This file proves a concrete implication needed by the structural chain. Its
premise is explicitly BO of every original generated table; the separate legal
purification theorem must establish that premise from the paper's global BO.
-/
namespace ComplexCSP
open MaltsevRelations BlockOrthogonality RowTypes

variable {D ι : Type} [Fintype D] {L : Language D ℂ ι}

/-- Literal original-table BO over all finite generated marginal tables.
Arity one is harmless; its matrix has only one row. This is not substituted for
the paper's joint-purification definition. -/
def AllGeneratedOriginalBO (L : Language D ℂ ι) : Prop :=
  ∀ (n : ℕ) (G : (Fin (n + 1) → D) → ℂ),
    Instance.Generated L G → TableBlockOrthogonal G

/-- Passing through a concrete finite-coordinate equivalence transfers support
rectangularity to arbitrary finite boundary types. -/
theorem allGeneratedOriginalBO_supportRectangular
    (hBO : AllGeneratedOriginalBO L) : AllGeneratedSupportRectangular L := by
  classical
  intro B _ _ G hG
  let eB : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  let eU : Unit ≃ Fin 1 := Fintype.equivFin Unit
  let e : B ⊕ Unit ≃ Fin (Fintype.card B + 1) :=
    (Equiv.sumCongr eB eU).trans finSumFinEquiv
  let F : (Fin (Fintype.card B + 1) → D) → ℂ := fun a => G (a ∘ e)
  have hF : Instance.Generated L F := Instance.generated_diagonal_minor hG e
  have hrect := blockOrthogonal_support_rectangular (hBO (Fintype.card B) F hF)
  have he (x : B → D) (z : D) :
      tableRows F (fun i => x (eB.symm i)) z = G (Sum.elim x (fun _ => z)) := by
    unfold tableRows F
    congr 1
    funext v
    rcases v with b | u
    · change Fin.snoc (α := fun _ : Fin (Fintype.card B + 1) => D) (fun i => x (eB.symm i)) z (eB b).castSucc = x b
      simp
    · have hu : eU u = 0 := Subsingleton.elim _ _
      change Fin.snoc (α := fun _ : Fin (Fintype.card B + 1) => D) (fun i => x (eB.symm i)) z (Fin.natAdd _ (eU u)) = z
      rw [hu]
      change Fin.snoc (α := fun _ : Fin (Fintype.card B + 1) => D) (fun i => x (eB.symm i)) z (Fin.last _) = z
      simp
  intro x y a b hxa hya hxb
  rw [← he y b]
  apply hrect (fun i => x (eB.symm i)) (fun i => y (eB.symm i)) a b
  · rw [he]
    exact hxa
  · rw [he]
    exact hya
  · rw [he]
    exact hxb

/-- Actual generated supports have one common operation once original-table BO
has been derived. The finite pp/repair/compactness chain is proved, not assumed. -/
theorem common_maltsev_of_allGeneratedOriginalBO [Nonempty D]
    (hBO : AllGeneratedOriginalBO L) :
    ∃ m : Operation D, IsMaltsev m ∧ CommonPolymorphism (generatedSupports L) m :=
  common_maltsev_of_generated_support_rectangularity
    (allGeneratedOriginalBO_supportRectangular hBO)

end ComplexCSP
