import ComplexCSP.Instances.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.Analysis.Complex.Basic

/-! # The actual common algebraic number field

This file establishes the mathematical field in Section 4 and proves all
literal generated values belong to it. The field and its basis are not presented
as an executable algebraic-number representation.
-/
namespace ComplexCSP

variable {D ι B H : Type}

namespace Language

/-- All input entries and their conjugates, with finite exact indexing. -/
def conjugateValues (L : Language D ℂ ι) : Set ℂ :=
  Set.range (fun p : (Σ i, Fin (L.arity i) → D) × Bool =>
    if p.2 then star (L.value p.1.1 p.1.2) else L.value p.1.1 p.1.2)

noncomputable def workingField (L : Language D ℂ ι) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ L.conjugateValues

theorem value_mem_workingField (L : Language D ℂ ι) (i : ι)
    (a : Fin (L.arity i) → D) : L.value i a ∈ L.workingField := by
  apply IntermediateField.subset_adjoin
  exact ⟨(⟨i, a⟩, false), rfl⟩

theorem star_value_mem_workingField (L : Language D ℂ ι) (i : ι)
    (a : Fin (L.arity i) → D) : star (L.value i a) ∈ L.workingField := by
  apply IntermediateField.subset_adjoin
  exact ⟨(⟨i, a⟩, true), rfl⟩

theorem conjugateValues_finite [Fintype D] [Fintype ι] (L : Language D ℂ ι) :
    L.conjugateValues.Finite := Set.finite_range _

/-- The actual input field is stable under complex conjugation. -/
theorem star_mem_workingField (L : Language D ℂ ι) {z : ℂ}
    (hz : z ∈ L.workingField) : star z ∈ L.workingField := by
  refine IntermediateField.adjoin_induction ℚ ?_ ?_ ?_ ?_ ?_ hz
  · rintro x ⟨⟨⟨i, a⟩, b⟩, rfl⟩
    cases b
    · exact L.star_value_mem_workingField i a
    · simpa only [Bool.true_eq_false, Bool.false_eq_true, if_false, if_true, star_star] using
        L.value_mem_workingField i a
  · intro q
    simpa using L.workingField.algebraMap_mem q
  · intro x y hx hy hxs hys
    simpa only [star_add] using L.workingField.add_mem hxs hys
  · intro x hx hxs
    simpa only [star_inv₀] using L.workingField.inv_mem hxs
  · intro x y hx hy hxs hys
    simpa only [star_mul] using L.workingField.mul_mem hys hxs

/-- Conjugation restricted to the mathematically constructed field. -/
noncomputable def workingFieldConj (L : Language D ℂ ι) :
    L.workingField ≃+* L.workingField where
  toFun z := ⟨star (z : ℂ), L.star_mem_workingField z.property⟩
  invFun z := ⟨star (z : ℂ), L.star_mem_workingField z.property⟩
  left_inv z := Subtype.ext (star_star _)
  right_inv z := Subtype.ext (star_star _)
  map_mul' x y := by apply Subtype.ext; simp [star_mul, mul_comm]
  map_add' x y := by apply Subtype.ext; simp

/-- The very same finite language, now taking values in its input-generated field. -/
noncomputable def workingFieldLanguage (L : Language D ℂ ι) :
    Language D L.workingField ι where
  arity := L.arity
  arity_pos := L.arity_pos
  value i a := ⟨L.value i a, L.value_mem_workingField i a⟩

@[simp] theorem workingFieldLanguage_coe (L : Language D ℂ ι) (i : ι)
    (a : Fin (L.arity i) → D) :
    ((L.workingFieldLanguage.value i a : L.workingField) : ℂ) = L.value i a := rfl

/-- Algebraicity of the finite generators, including conjugation. -/
theorem conjugateValues_integral (L : Language D ℂ ι)
    (hL : ∀ i a, IsAlgebraic ℚ (L.value i a)) :
    ∀ z ∈ L.conjugateValues, IsIntegral ℚ z := by
  rintro z ⟨⟨⟨i, a⟩, b⟩, rfl⟩
  cases b
  · exact (hL i a).isIntegral
  · exact IsIntegral.map (Complex.conjAe.restrictScalars ℚ) (hL i a).isIntegral

/-- The input-generated conjugation-stable field is a genuine finite extension
of the rationals, not an abstract field supplied as an assumed oracle. -/
theorem workingField_finiteDimensional [Fintype D] [Fintype ι]
    (L : Language D ℂ ι) (hL : ∀ i a, IsAlgebraic ℚ (L.value i a)) :
    FiniteDimensional ℚ L.workingField := by
  letI : Finite L.conjugateValues := L.conjugateValues_finite.to_subtype
  exact IntermediateField.finiteDimensional_adjoin (L.conjugateValues_integral hL)

theorem workingField_numberField [Fintype D] [Fintype ι]
    (L : Language D ℂ ι) (hL : ∀ i a, IsAlgebraic ℚ (L.value i a)) :
    NumberField L.workingField := by
  letI := L.workingField_finiteDimensional hL
  exact ⟨⟩

end Language

namespace Instance
variable {L : Language D ℂ ι}

theorem eval_mem_workingField (I : Instance L B H) (a : B → D) (b : H → D) :
    I.eval a b ∈ L.workingField := by
  unfold eval
  apply L.workingField.toSubalgebra.toSubsemiring.list_prod_mem
  intro z hz
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hz
  exact L.value_mem_workingField c.symbol _

theorem partition_mem_workingField [Fintype D] [Fintype H] [DecidableEq H]
    (I : Instance L B H) (a : B → D) : I.partition a ∈ L.workingField := by
  apply L.workingField.sum_mem
  intro b _
  exact I.eval_mem_workingField a b

/-- Every entry of every unbounded generated table is in the one input field. -/
theorem generated_mem_workingField [Fintype D]
    {G : (B → D) → ℂ} (hG : Generated L G) (a : B → D) : G a ∈ L.workingField := by
  obtain ⟨n, I, hI⟩ := hG
  rw [← hI a]
  exact I.partition_mem_workingField a

end Instance
end ComplexCSP
