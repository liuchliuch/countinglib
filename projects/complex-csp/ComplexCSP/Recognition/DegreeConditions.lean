import ComplexCSP.Structure.DegreeStructuralSupport
import ComplexCSP.Recognition.DegreeConditionsOrdered
import ComplexCSP.Recognition.GlobalConditions

/-! # Genuine degree-multiple joint Block Orthogonality

The finite tuples use exactly the ordinary legal ambient purification, but their
membership witnesses are required to have every occurrence degree divisible by δ.
No unrestricted joint-BO premise enters these definitions or proofs.
-/
namespace ComplexCSP
open BlockOrthogonality RowTypes GeneratingSet MaltsevRelations
open Purification.PurificationMap

variable {D ι : Type} [Fintype D] (L : Language D ℂ ι) (δ : ℕ)

/-- Literal nonempty joint tuples of distinct degree-generated positive tables. -/
def DegreeJointBO : Prop :=
  ∀ (h : ℕ), 0 < h → ∀ (Ts : Fin h → PositiveTable D),
    Function.Injective Ts → (∀ i, DegreeGenerated L δ (Ts i).value) →
      ∀ i, 0 < (Ts i).rowArity → BlockOrthogonal (jointRows D Ts i)

/-- The degree membership quantifier is exactly the paper's ordered partial
marginal family, not an enlarged semantic closure. -/
theorem degreeJointBO_iff_ordered : DegreeJointBO L δ ↔
    ∀ (h : ℕ), 0 < h → ∀ (Ts : Fin h → PositiveTable D),
      Function.Injective Ts → (∀ i, PaperDegreeGenerated L δ (Ts i).value) →
        ∀ i, 0 < (Ts i).rowArity → BlockOrthogonal (jointRows D Ts i) := by
  simp only [DegreeJointBO, degreeGenerated_iff_paperDegreeGenerated]

/-- The singleton condition uses the same legal prime map as the full joint one. -/
def DegreeSingletonBO : Prop :=
  ∀ T : PositiveTable D, DegreeGenerated L δ T.value → 0 < T.rowArity →
    BlockOrthogonal T.singletonRows

/-- Actual arbitrary-ambient invariance proves the degree version of Corollary 3.2. -/
theorem degreeJointBO_iff_singletonBO : DegreeJointBO L δ ↔ DegreeSingletonBO L δ := by
  constructor
  · intro h T hT hpos
    let Ts : Fin 1 → PositiveTable D := fun _ => T
    have hi : Function.Injective Ts := fun _ _ _ => Subsingleton.elim _ _
    have hb := h 1 (by omega) Ts hi (fun _ => hT) 0 hpos
    exact (T.ambient_BO_iff
      (LegalGeneratingSet.choose (jointValues D Ts))
      (LegalGeneratingSet.choose T.nonzeroValues)
      (nonzeroValues_subset_joint D Ts 0) (Finset.Subset.refl _)).mp hb
  · intro h n hn Ts hi hTs i hpos
    have hb := h (Ts i) (hTs i) hpos
    exact ((Ts i).ambient_BO_iff
      (LegalGeneratingSet.choose (jointValues D Ts))
      (LegalGeneratingSet.choose (Ts i).nonzeroValues)
      (nonzeroValues_subset_joint D Ts i) (Finset.Subset.refl _)).mpr hb

/-- At δ = 1 the genuine joint definition is exactly the ordinary one. -/
theorem degreeJointBO_one_iff : DegreeJointBO L 1 ↔ JointBO L := by
  simp only [DegreeJointBO, JointBO, DegreeGenerated.at_one_iff]

/-- Original BO is needed and proved only for degree-generated tables. -/
def AllDegreeGeneratedOriginalBO : Prop :=
  ∀ (n : ℕ) (G : (Fin (n + 1) → D) → ℂ),
    DegreeGenerated L δ G → TableBlockOrthogonal G

/-- Legal singleton purification transfers back to each original degree table. -/
theorem DegreeJointBO.original (h : DegreeJointBO L δ) :
    AllDegreeGeneratedOriginalBO L δ := by
  intro n G hG
  cases n with
  | zero => exact blockOrthogonal_subsingleton_rows (tableRows G)
  | succ n =>
    let T : PositiveTable D := ⟨n + 1, G⟩
    have hp := (degreeJointBO_iff_singletonBO L δ).mp h T hG (Nat.succ_pos n)
    unfold PositiveTable.singletonRows PositiveTable.purifiedRows at hp
    exact original_blockOrthogonal_of_purified T.rows _ hp

/-- Passing through a concrete finite-coordinate equivalence transfers support
rectangularity to arbitrary finite boundary types. -/
theorem allDegreeGeneratedOriginalBO_supportRectangular
    (hBO : AllDegreeGeneratedOriginalBO L δ) : AllDegreeGeneratedSupportRectangular L δ := by
  classical
  intro B _ _ G hG
  let eB : B ≃ Fin (Fintype.card B) := Fintype.equivFin B
  let eU : Unit ≃ Fin 1 := Fintype.equivFin Unit
  let e : B ⊕ Unit ≃ Fin (Fintype.card B + 1) :=
    (Equiv.sumCongr eB eU).trans finSumFinEquiv
  let F : (Fin (Fintype.card B + 1) → D) → ℂ := fun a => G (a ∘ e)
  have hF : DegreeGenerated L δ F := DegreeGenerated.diagonal_minor hG e
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

/-- One Mal'tsev operation for the full degree-generated support family follows
from actual pp closure, finite repair, and finite-candidate compactness. -/
theorem DegreeJointBO.common_support_maltsev [Nonempty D] (h : DegreeJointBO L δ) :
    ∃ m : Operation D, IsMaltsev m ∧ CommonPolymorphism (degreeGeneratedSupports L δ) m :=
  common_maltsev_of_degree_generated_support_rectangularity
    (allDegreeGeneratedOriginalBO_supportRectangular L δ (h.original L δ))

end ComplexCSP
