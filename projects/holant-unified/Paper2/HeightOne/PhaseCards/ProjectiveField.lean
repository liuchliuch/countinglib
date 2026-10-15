import Paper2.HeightOne.PhaseCards.FactorSaturation

/-! Prime factors of an L-valued tensor are projectively L-valued, regardless
of which algebraic prime decomposition was selected. This prevents arbitrary
factor normalizations from enlarging the frozen coefficient field. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable
open scoped BigOperators
variable {K : Type*} [Field K] {ι κ : Type*}

/-- One scalar for the entire tensor puts all coefficients in the same field. -/
def ProjectivelyOver (L : Subfield K) (f : Tensor K ι) : Prop :=
  ∃ c : K, c ≠ 0 ∧ ∀ x, c * f x ∈ L

lemma ProjectivelyOver.reindex {L : Subfield K} {f : Tensor K ι}
    (hf : ProjectivelyOver L f) (e : ι ≃ κ) :
    ProjectivelyOver L (Tensor.reindex e f) := by
  obtain ⟨c, hc, h⟩ := hf
  exact ⟨c, hc, fun x => h (x ∘ e)⟩

lemma ProjectivelyOver.scale {L : Subfield K} {f : Tensor K ι}
    (hf : ProjectivelyOver L f) {a : K} (ha : a ≠ 0) :
    ProjectivelyOver L (a • f) := by
  obtain ⟨c, hc, h⟩ := hf
  refine ⟨c / a, div_ne_zero hc ha, ?_⟩
  intro x
  convert h x using 1
  simp [div_eq_mul_inv, mul_assoc, ha]

namespace Decomposition
variable {n : ℕ} (D : TensorDecomposition K n)

/-- Replace exactly one factor's ordered assignment, preserving all other
factor assignments. The recorded port equivalence implements the literal cut. -/
def replaceWord (z : Fin n → Bool) (i : Fin D.count)
    (y : Fin (D.arity i) → Bool) : Fin n → Bool :=
  D.assignments.symm (Function.update (D.assignments z) i y)

lemma assignments_replaceWord (z : Fin n → Bool) (i : Fin D.count)
    (y : Fin (D.arity i) → Bool) :
    D.assignments (replaceWord D z i y) = Function.update (D.assignments z) i y :=
  D.assignments.apply_symm_apply _

lemma value_replaceWord (z : Fin n → Bool) (i : Fin D.count)
    (y : Fin (D.arity i) → Bool) :
    D.value (replaceWord D z i y) * D.factor i (D.assignments z i) =
      D.value z * D.factor i y := by
  classical
  have hvalue (x : Fin n → Bool) :
      D.value x = (D.scale : K) * ∏ j, D.factor j (D.assignments x j) := rfl
  rw [hvalue, assignments_replaceWord, hvalue]
  rw [← Finset.mul_prod_erase (Finset.univ) (fun j => D.factor j
    (Function.update (D.assignments z) i y j)) (Finset.mem_univ i)]
  rw [← Finset.mul_prod_erase (Finset.univ) (fun j => D.factor j
    (D.assignments z j)) (Finset.mem_univ i)]
  rw [Function.update_self]
  have he : (∏ j ∈ Finset.univ.erase i, D.factor j (Function.update (D.assignments z) i y j)) =
      ∏ j ∈ Finset.univ.erase i, D.factor j (D.assignments z j) := by
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
  rw [he]
  ring

/-- Every selected factor descends projectively to the original coefficient
field. Primality is unnecessary: this holds for every actual tensor factor. -/
theorem factor_projectivelyOver (L : Subfield K)
    (hf : ProjectivelyOver L D.value) (hn : D.value ≠ 0) (i : Fin D.count) :
    ProjectivelyOver L (D.factor i) := by
  classical
  obtain ⟨z, hz⟩ : ∃ z, D.value z ≠ 0 := by
    by_contra h
    push_neg at h
    exact hn (funext h)
  obtain ⟨c, hc, hL⟩ := hf
  have hi : D.factor i (D.assignments z i) ≠ 0 := by
    intro hi
    apply hz
    change (D.scale : K) * (∏ j, D.factor j (D.assignments z j)) = 0
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, mul_zero]
  refine ⟨(D.factor i (D.assignments z i))⁻¹, inv_ne_zero hi, ?_⟩
  intro y
  have he : (D.factor i (D.assignments z i))⁻¹ * D.factor i y =
      (c * D.value (replaceWord D z i y)) / (c * D.value z) := by
    apply (eq_div_iff (mul_ne_zero hc hz)).mpr
    have h := value_replaceWord D z i y
    field_simp [hi]
    linear_combination -h
  rw [he]
  exact L.div_mem (hL _) (hL _)

end Decomposition

/-- Projective coefficient-field control is preserved by actual bilinear
contraction; the product of the two normalization scalars is kept. -/
lemma projectivelyOver_contractKernel [Fintype ι] (L : Subfield K)
    (E : Kernel K) (f : Tensor K (ι ⊕ Bool))
    (hE : ∃ c : K, c ≠ 0 ∧ ∀ a b, c * E a b ∈ L)
    (hf : ProjectivelyOver L f) : ProjectivelyOver L (contractKernel E f) := by
  classical
  obtain ⟨a, ha, hE⟩ := hE
  obtain ⟨b, hb, hf⟩ := hf
  refine ⟨a * b, mul_ne_zero ha hb, ?_⟩
  intro x
  have he : (a * b) * contractKernel E f x =
      ∑ v : Bool → Bool, (a * E (v false) (v true)) * (b * f (Sum.elim x v)) := by
    simp only [contractKernel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    ring
  rw [he]
  exact L.sum_mem (fun v _ => L.mul_mem (hE _ _) (hf _))

end
end Paper2.HeightOne.PhaseCards
