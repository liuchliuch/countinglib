import Counting.Algorithm.KarpLuby.DNFSampling
import Counting.Algorithm.KarpLuby.FiniteCover
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin

/-!
# The cover represented by an explicit DNF formula

These finite sets describe denotations only. Constructing all assignments is not
claimed as the polynomial implementation: clause sampling uses the separate
unranking implementation. The explicit ambient variable count is preserved.
-/

namespace Counting.Algorithm.KarpLuby.DNF

open scoped BigOperators

variable {n : ℕ}

/-- Finite denotation of a normalized, consistent clause. -/
def clauseAssignments (c : Clause n) : Finset (Assignment n) :=
  Finset.univ.filter (Satisfies c)

/-- Finite denotation of the original formula, before normalization. -/
def satisfyingAssignments (f : Formula n) : Finset (Assignment n) :=
  Finset.univ.filter fun a => evalDNF f a = true

/-- The desired count includes every one of the explicit ambient variables. -/
def modelCount (f : Formula n) : ℕ := (satisfyingAssignments f).card

/-- Index by list positions, preserving the multiplicity of repeated clauses. -/
def clauseFamily (cs : List (Clause n)) : Fin cs.length → Finset (Assignment n) :=
  fun i => clauseAssignments (cs.get i)

/-- Reject contradictory terms, then retain every remaining term occurrence. -/
def normalizedCover (f : Formula n) :
    Fin (normalizeFormula f).length → Finset (Assignment n) :=
  clauseFamily (normalizeFormula f)

@[simp] theorem mem_clauseAssignments (c : Clause n) (a : Assignment n) :
    a ∈ clauseAssignments c ↔ Satisfies c a := by
  simp [clauseAssignments]

/-- The executable clause mass equals its full ambient denotation cardinality. -/
@[simp] theorem card_clauseAssignments (c : Clause n) :
    (clauseAssignments c).card = clauseMass c := by
  simpa only [Fintype.card_subtype, clauseAssignments, clauseMass] using card_satisfies c

theorem clauseAssignments_nonempty (c : Clause n) : (clauseAssignments c).Nonempty := by
  rw [← Finset.card_pos, card_clauseAssignments]
  exact clauseMass_pos c

@[simp] theorem mem_satisfyingAssignments (f : Formula n) (a : Assignment n) :
    a ∈ satisfyingAssignments f ↔ evalDNF f a = true := by
  simp [satisfyingAssignments]

@[simp] theorem mem_clauseFamily (cs : List (Clause n)) (i : Fin cs.length)
    (a : Assignment n) : a ∈ clauseFamily cs i ↔ Satisfies (cs.get i) a := by
  simp [clauseFamily]

@[simp] theorem mem_coverUnion_clauseFamily (cs : List (Clause n)) (a : Assignment n) :
    a ∈ coverUnion (clauseFamily cs) ↔ ∃ c ∈ cs, Satisfies c a := by
  rw [mem_coverUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨cs.get i, List.get_mem cs i, (mem_clauseFamily cs i a).mp hi⟩
  · rintro ⟨c, hc, ha⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hc
    exact ⟨i, (mem_clauseFamily cs i a).mpr ha⟩

/-- The semantic tagged mass is the prefix-sampler's concrete list sum. -/
theorem mass_clauseFamily (cs : List (Clause n)) :
    mass (clauseFamily cs) = (cs.map clauseMass).sum := by
  simp [mass, clauseFamily, List.get_eq_getElem]

theorem mass_clauseFamily_le (cs : List (Clause n)) :
    mass (clauseFamily cs) ≤ cs.length * 2 ^ n := by
  calc
    mass (clauseFamily cs) = ∑ i : Fin cs.length, clauseMass (cs.get i) := by
      simp [mass, clauseFamily]
    _ ≤ ∑ _i : Fin cs.length, 2 ^ n :=
      Finset.sum_le_sum fun i _ => clauseMass_le (cs.get i)
    _ = cs.length * 2 ^ n := by simp

/-- A list of consistent clauses has positive mass unless it is empty. -/
theorem mass_clauseFamily_eq_zero_iff (cs : List (Clause n)) :
    mass (clauseFamily cs) = 0 ↔ cs = [] := by
  rw [mass_clauseFamily]
  cases cs with
  | nil => simp
  | cons c cs =>
    have hc := clauseMass_pos c
    simp only [List.map_cons, List.sum_cons, reduceCtorEq, iff_false]
    omega

/-- Normalization followed by the cover construction preserves the original formula. -/
@[simp] theorem mem_normalizedCover_union (f : Formula n) (a : Assignment n) :
    a ∈ coverUnion (normalizedCover f) ↔ evalDNF f a = true := by
  rw [normalizedCover, mem_coverUnion_clauseFamily, normalizeFormula_correct]

/-- The bridge is equality of finite denotations, not just equality of counts. -/
theorem normalizedCover_union (f : Formula n) :
    coverUnion (normalizedCover f) = satisfyingAssignments f := by
  ext a
  exact (mem_normalizedCover_union f a).trans (mem_satisfyingAssignments f a).symm

@[simp] theorem count_normalizedCover (f : Formula n) :
    count (normalizedCover f) = modelCount f := by
  simp [count, modelCount, normalizedCover_union]

/-- Every satisfying assignment has exactly one accepted tagged occurrence. -/
theorem card_DNF_ownerEvent (f : Formula n) :
    (ownerEvent (normalizedCover f)).card = modelCount f := by
  rw [card_ownerEvent, count_normalizedCover]

/-- The owner predicate tests only preceding normalized term occurrences. -/
theorem isOwner_normalizedCover (f : Formula n)
    (i : Fin (normalizeFormula f).length) (a : Assignment n) :
    IsOwner (normalizedCover f) ⟨i, a⟩ ↔
      ∀ j, j < i → ¬ Satisfies ((normalizeFormula f).get j) a := by
  simp [IsOwner, normalizedCover]

/-- Removing rejected terms never increases the number of occurrences. -/
theorem normalizeFormula_length_le (f : Formula n) :
    (normalizeFormula f).length ≤ f.length := by
  exact List.length_filterMap_le _ _

theorem modelCount_le_mass (f : Formula n) :
    modelCount f ≤ mass (normalizedCover f) := by
  rw [← count_normalizedCover]
  exact count_le_mass _

/-- The overlap factor is at most the number of original term occurrences. -/
theorem mass_normalizedCover_le (f : Formula n) :
    mass (normalizedCover f) ≤ f.length * modelCount f := by
  calc
    mass (normalizedCover f) ≤ (normalizeFormula f).length * count (normalizedCover f) :=
      mass_le_mul_count _
    _ = (normalizeFormula f).length * modelCount f := by rw [count_normalizedCover]
    _ ≤ f.length * modelCount f :=
      Nat.mul_le_mul_right _ (normalizeFormula_length_le f)

/-- An unsatisfiable formula has zero tagged mass, making the exact-zero branch decidable. -/
theorem modelCount_eq_zero_iff_mass_eq_zero (f : Formula n) :
    modelCount f = 0 ↔ mass (normalizedCover f) = 0 := by
  rw [← count_normalizedCover]
  exact count_eq_zero_iff_mass_eq_zero _

/-- Normalization is also an exact satisfiability test for DNF. -/
theorem modelCount_eq_zero_iff_normalizeFormula (f : Formula n) :
    modelCount f = 0 ↔ normalizeFormula f = [] := by
  rw [modelCount_eq_zero_iff_mass_eq_zero]
  exact mass_clauseFamily_eq_zero_iff _

@[simp] theorem satisfyingAssignments_nil : satisfyingAssignments ([] : Formula n) = ∅ := by
  ext a
  simp [evalDNF]

@[simp] theorem modelCount_nil : modelCount ([] : Formula n) = 0 := by
  simp [modelCount]

/-- An empty conjunction leaves all explicit variables free. -/
theorem satisfyingAssignments_of_empty_term (f : Formula n) (h : [] ∈ f) :
    satisfyingAssignments f = Finset.univ := by
  ext a
  simp only [mem_satisfyingAssignments, Finset.mem_univ, iff_true, evalDNF_eq_true]
  exact ⟨[], h, evalTerm_nil a⟩

theorem modelCount_of_empty_term (f : Formula n) (h : [] ∈ f) :
    modelCount f = 2 ^ n := by
  rw [modelCount, satisfyingAssignments_of_empty_term f h]
  simp [Assignment]

/-- Repeating a term preserves the model count while the cover still retains both occurrences. -/
theorem satisfyingAssignments_duplicate (t : RawTerm n) (f : Formula n) :
    satisfyingAssignments (t :: t :: f) = satisfyingAssignments (t :: f) := by
  ext a
  simp [evalDNF]

theorem modelCount_duplicate (t : RawTerm n) (f : Formula n) :
    modelCount (t :: t :: f) = modelCount (t :: f) := by
  rw [modelCount, satisfyingAssignments_duplicate, modelCount]

/-- A term rejected by normalization contributes no assignments. -/
theorem satisfyingAssignments_rejected (t : RawTerm n) (f : Formula n)
    (h : normalize t = none) :
    satisfyingAssignments (t :: f) = satisfyingAssignments f := by
  ext a
  have ht : evalTerm t a ≠ true := by
    intro ha
    have hn := (normalize_correct t a).mpr ha
    simp [h] at hn
  simp [evalDNF, ht]

theorem modelCount_rejected (t : RawTerm n) (f : Formula n)
    (h : normalize t = none) : modelCount (t :: f) = modelCount f := by
  rw [modelCount, satisfyingAssignments_rejected t f h, modelCount]

end Counting.Algorithm.KarpLuby.DNF
