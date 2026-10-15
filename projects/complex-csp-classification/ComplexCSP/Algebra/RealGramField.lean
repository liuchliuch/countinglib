import ComplexCSP.Complexity.ReducedGram

/-! # The actual ordered real subfield of a constructed Gram obstruction

Only matrix entries are adjoined. Its real order is inherited from ℝ, and the
embedding into the common complex coefficient field is constructed by adjoin
induction. No embedding or algebraicity certificate is supplied by a caller.
-/
noncomputable section
open Classical
namespace ComplexCSP.RealGramField
open scoped BigOperators
open ComplexityReducedGram
variable {D : Type} [Fintype D] {s : ℕ} {L : Language D ℂ (Fin s)} (W : Witness L)

def generators : Set ℝ := Set.range (fun p : Fin W.colors × Fin W.colors => (W.matrix p.1 p.2 : ℂ).re)
def field : IntermediateField ℚ ℝ := IntermediateField.adjoin ℚ (generators W)

theorem ofReal_entry (i j : Fin W.colors) :
    (((W.matrix i j : ℂ).re : ℝ) : ℂ) = (W.matrix i j : ℂ) := by
  apply Complex.ext
  · rfl
  · exact (W.real_entries i j).symm

theorem finiteDimensional : FiniteDimensional ℚ (field W) := by
  letI : FiniteDimensional ℚ W.field := W.fieldFinite
  letI : Finite (generators W) := (Set.finite_range
    (fun p : Fin W.colors × Fin W.colors => (W.matrix p.1 p.2 : ℂ).re)).to_subtype
  apply IntermediateField.finiteDimensional_adjoin
  rintro z ⟨⟨i,j⟩,rfl⟩
  have hi : IsIntegral ℚ (W.matrix i j) := IsIntegral.of_finite (R:=ℚ) (W.matrix i j)
  have hc : IsIntegral ℚ (W.matrix i j : ℂ) := IsIntegral.map W.field.val hi
  apply (isIntegral_algebraMap_iff (R:=ℚ) (A:=ℝ) (B:=ℂ)).mp
  change IsIntegral ℚ ((((W.matrix i j : ℂ).re : ℝ) : ℂ))
  rw [ofReal_entry]
  exact hc

def basis : Module.Basis (Fin (Module.finrank ℚ (field W))) ℚ (field W) := by
  letI := finiteDimensional W
  exact Module.finBasis ℚ (field W)

theorem ofReal_mem {x : ℝ} (hx : x ∈ field W) : (x : ℂ) ∈ W.field := by
  refine IntermediateField.adjoin_induction ℚ ?_ ?_ ?_ ?_ ?_ hx
  · rintro x ⟨⟨i,j⟩,rfl⟩
    rw [ofReal_entry]
    exact (W.matrix i j).property
  · intro q
    simpa using W.field.algebraMap_mem q
  · intro x y hx hy hxc hyc
    simpa only [Complex.ofReal_add] using W.field.add_mem hxc hyc
  · intro x hx hxc
    simpa only [Complex.ofReal_inv] using W.field.inv_mem hxc
  · intro x y hx hy hxc hyc
    simpa only [Complex.ofReal_mul] using W.field.mul_mem hxc hyc

def embedding : field W →+* W.field where
  toFun x := ⟨((x : ℝ) : ℂ),ofReal_mem W x.property⟩
  map_zero' := Subtype.ext (by simp)
  map_one' := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)

def matrix (i j : Fin W.colors) : field W :=
  ⟨(W.matrix i j : ℂ).re,IntermediateField.subset_adjoin ℚ (generators W) ⟨(i,j),rfl⟩⟩

@[simp] theorem embedding_matrix (i j : Fin W.colors) : embedding W (matrix W i j)=W.matrix i j :=
  Subtype.ext (ofReal_entry W i j)

theorem matrix_symmetric (i j : Fin W.colors) : matrix W i j=matrix W j i := by
  apply (embedding W).injective
  simp only [embedding_matrix,W.symmetric]

theorem matrix_nonnegative (i j : Fin W.colors) : 0 ≤ matrix W i j := W.nonnegative_entries i j

theorem matrix_gram (i j : Fin W.colors) :
    (matrix W i j : ℝ)=∑ z,W.factor i z*W.factor j z := by
  change (W.matrix i j : ℂ).re = _
  rw [W.gram]
  rfl

theorem norm_entry (i j : Fin W.colors) : ‖(W.matrix i j : ℂ)‖=(matrix W i j : ℝ) := by
  rw [←ofReal_entry W i j]
  simp only [Complex.norm_real,Real.norm_eq_abs]
  exact abs_of_nonneg (W.nonnegative_entries i j)

theorem strict_minor : ∃ i j,0 < matrix W i i ∧ 0 < matrix W i j ∧ 0 < matrix W j j ∧
    matrix W i j*matrix W j i < matrix W i i*matrix W j j := by
  obtain ⟨i,j,hii,hij,hjj,hdet⟩ := W.obstruction
  refine ⟨i,j,?_⟩
  change 0 < (matrix W i i : ℝ) ∧ 0 < (matrix W i j : ℝ) ∧
    0 < (matrix W j j : ℝ) ∧
      (matrix W i j : ℝ)*(matrix W j i : ℝ) < (matrix W i i : ℝ)*(matrix W j j : ℝ)
  simpa only [norm_entry] using And.intro hii (And.intro hij (And.intro hjj hdet))

end ComplexCSP.RealGramField
