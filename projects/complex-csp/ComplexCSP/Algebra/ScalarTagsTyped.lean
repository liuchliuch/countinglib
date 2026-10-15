import Mathlib.Algebra.Module.Rat
import Mathlib.Algebra.Module.Pi
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.NoZeroSMulDivisors.Basic
import Mathlib.Logic.Encodable.Pi

/-!
# Common tags for typed families

The dependent-arity form of Lemma 5.4, with a total sequential search over
encoded finite vectors of positive integer tags. This complements ScalarTags.
-/
namespace ComplexCSP.ScalarTags
variable {K V : Type*} [Field K] [CharZero K]
variable [AddCommGroup V] [Module K V]

theorem finite_collision (v w : V) (hw : v ≠ 0 ∨ w ≠ 0) (m : ℕ) :
    {n : ℕ | ((n + 1 : ℕ) : K) • v = ((m + 1 : ℕ) : K) • w}.Finite := by
  by_cases hv : v = 0
  · have hw' : w ≠ 0 := hw.resolve_left (not_ne_iff.mpr hv)
    subst v
    have hm : ((m + 1 : ℕ) : K) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
    have he : {n : ℕ | ((n + 1 : ℕ) : K) • (0 : V) =
        ((m + 1 : ℕ) : K) • w} = ∅ := by
      ext n
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, smul_zero]
      exact (smul_ne_zero hm hw').symm
    rw [he]
    exact Set.finite_empty
  · have hi : Function.Injective (fun n : ℕ => ((n + 1 : ℕ) : K) • v) := by
      intro n k h
      have he := (smul_left_injective K hv) h
      have hn : n + 1 = k + 1 := Nat.cast_injective he
      omega
    exact (Set.finite_singleton (((m + 1 : ℕ) : K) • w)).preimage hi.injOn

section Families
variable {ι W : Type*} [AddCommGroup W] [Module K W]

def Good (R : ι → ι → Prop) (h : ι → V) (g : ι → W) (s : Finset ι)
    (tag : ι → ℕ) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, i ≠ j → R i j →
    (((tag i + 1 : ℕ) : K) • h i ≠ ((tag j + 1 : ℕ) : K) • h j) ∧
    (((tag i + 1 : ℕ) : K) • g i ≠ ((tag j + 1 : ℕ) : K) • g j)

/-- Finite avoidance for a symmetric compatibility relation; equality of arity
is the intended compatibility. -/
theorem exists_common_tags_finset (R : ι → ι → Prop) (hR : Symmetric R)
    (h : ι → V) (g : ι → W)
    (hh : ∀ i j, i ≠ j → R i j → h i ≠ 0 ∨ h j ≠ 0)
    (hg : ∀ i j, i ≠ j → R i j → g i ≠ 0 ∨ g j ≠ 0)
    (s : Finset ι) : ∃ tag : ι → ℕ, Good (K := K) R h g s tag := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨fun _ => 0, by simp [Good]⟩
  | @insert a s ha ih =>
    obtain ⟨tag, ht⟩ := ih
    let bad : ι → Set ℕ := fun j =>
      if R a j then
        {n | ((n + 1 : ℕ) : K) • h a = ((tag j + 1 : ℕ) : K) • h j} ∪
        {n | ((n + 1 : ℕ) : K) • g a = ((tag j + 1 : ℕ) : K) • g j}
      else ∅
    have hbad : ∀ j ∈ s, (bad j).Finite := by
      intro j hj
      have haj : a ≠ j := by rintro rfl; exact ha hj
      by_cases hr : R a j
      · simp only [bad, if_pos hr]
        exact (finite_collision _ _ (hh a j haj hr) _).union
          (finite_collision _ _ (hg a j haj hr) _)
      · simp [bad, hr]
    have hfinite : (⋃ j ∈ (s : Set ι), bad j).Finite :=
      s.finite_toSet.biUnion hbad
    obtain ⟨n, hn⟩ := hfinite.exists_notMem
    have hnew : ∀ j ∈ s, R a j →
        (((n + 1 : ℕ) : K) • h a ≠ ((tag j + 1 : ℕ) : K) • h j) ∧
        (((n + 1 : ℕ) : K) • g a ≠ ((tag j + 1 : ℕ) : K) • g j) := by
      intro j hj hr
      have hjn : n ∉ bad j := by
        intro he
        exact hn (Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨hj, he⟩⟩)
      simpa only [bad, if_pos hr, Set.mem_union, Set.mem_ofPred_eq, not_or] using hjn
    refine ⟨Function.update tag a n, ?_⟩
    intro i hi j hj hij hr
    by_cases hia : i = a
    · subst i
      have hja : j ≠ a := hij.symm
      have hj' : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hja
      simpa only [Function.update_self, Function.update_of_ne hja] using hnew j hj' hr
    · have hi' : i ∈ s := (Finset.mem_insert.mp hi).resolve_left hia
      by_cases hja : j = a
      · subst j
        obtain ⟨hh', hg'⟩ := hnew i hi' (hR hr)
        simpa only [Function.update_self, Function.update_of_ne hia] using
          And.intro hh'.symm hg'.symm
      · have hj' : j ∈ s := (Finset.mem_insert.mp hj).resolve_left hja
        simpa only [Function.update_of_ne hia, Function.update_of_ne hja] using
          ht i hi' j hj' hij hr

theorem exists_common_tags [Fintype ι] (R : ι → ι → Prop) (hR : Symmetric R)
    (h : ι → V) (g : ι → W)
    (hh : ∀ i j, i ≠ j → R i j → h i ≠ 0 ∨ h j ≠ 0)
    (hg : ∀ i j, i ≠ j → R i j → g i ≠ 0 ∨ g j ≠ 0) :
    ∃ tag : ι → ℕ, ∀ i j, i ≠ j → R i j →
      (((tag i + 1 : ℕ) : K) • h i ≠ ((tag j + 1 : ℕ) : K) • h j) ∧
      (((tag i + 1 : ℕ) : K) • g i ≠ ((tag j + 1 : ℕ) : K) • g j) := by
  obtain ⟨tag, ht⟩ := exists_common_tags_finset (K := K) R hR h g hh hg Finset.univ
  exact ⟨tag, fun i j hij hr => ht i (Finset.mem_univ _) j (Finset.mem_univ _) hij hr⟩
end Families

section DependentFamilies
variable {ι : Type*} [Fintype ι] {E F : ℕ → Type*}
variable [∀ r, AddCommGroup (E r)] [∀ r, Module K (E r)]
variable [∀ r, AddCommGroup (F r)] [∀ r, Module K (F r)]

/-- Proof-only embedding of all arities into a common vector space. -/
def packValue (x : (r : ℕ) × E r) : (r : ℕ) → E r :=
  fun r => if he : x.1 = r then he ▸ x.2 else 0

@[simp] theorem packValue_same (r : ℕ) (x : E r) :
    packValue ⟨r, x⟩ r = x := by simp [packValue]

theorem packValue_ne_zero (r : ℕ) (x : E r) (hx : x ≠ 0) :
    packValue ⟨r, x⟩ ≠ 0 := by
  intro he
  have := congrFun he r
  exact hx (by simpa using this)

omit [CharZero K] in
@[simp] theorem packValue_smul (c : K) (r : ℕ) (x : E r) :
    packValue ⟨r, c • x⟩ = c • packValue ⟨r, x⟩ := by
  funext t
  by_cases he : r = t
  · subst t; simp [packValue]
  · simp [packValue, he]

/-- One common positive integer tag per symbol separates both varying-arity
families; each arity can have its own one zero table in each family. -/
theorem exists_common_typed_tags (arity : ι → ℕ)
    (h : (i : ι) → E (arity i)) (g : (i : ι) → F (arity i))
    (hh : ∀ i j, i ≠ j → arity i = arity j → h i ≠ 0 ∨ h j ≠ 0)
    (hg : ∀ i j, i ≠ j → arity i = arity j → g i ≠ 0 ∨ g j ≠ 0) :
    ∃ tag : ι → ℕ,
      Function.Injective (fun i => (⟨arity i, ((tag i + 1 : ℕ) : K) • h i⟩ : (r : ℕ) × E r)) ∧
      Function.Injective (fun i => (⟨arity i, ((tag i + 1 : ℕ) : K) • g i⟩ : (r : ℕ) × F r)) := by
  let H : ι → (r : ℕ) → E r := fun i => packValue ⟨arity i, h i⟩
  let G : ι → (r : ℕ) → F r := fun i => packValue ⟨arity i, g i⟩
  have hH : ∀ i j, i ≠ j → arity i = arity j → H i ≠ 0 ∨ H j ≠ 0 := by
    intro i j hij ha
    exact (hh i j hij ha).imp (packValue_ne_zero _ _) (packValue_ne_zero _ _)
  have hG : ∀ i j, i ≠ j → arity i = arity j → G i ≠ 0 ∨ G j ≠ 0 := by
    intro i j hij ha
    exact (hg i j hij ha).imp (packValue_ne_zero _ _) (packValue_ne_zero _ _)
  obtain ⟨tag, ht⟩ := exists_common_tags (K := K) (fun i j => arity i = arity j)
    (fun _ _ he => he.symm) H G hH hG
  refine ⟨tag, ?_, ?_⟩
  · intro i j he
    by_contra hij
    have ha : arity i = arity j := congrArg Sigma.fst he
    have hpacked := congrArg (packValue (E := E)) he
    exact (ht i j hij ha).1 (by simpa [H] using hpacked)
  · intro i j he
    by_contra hij
    have ha : arity i = arity j := congrArg Sigma.fst he
    have hpacked := congrArg (packValue (E := F)) he
    exact (ht i j hij ha).2 (by simpa [G] using hpacked)

/-- The literal positive-rational existence assertion of Lemma 5.4. -/
theorem exists_common_rational_tags (arity : ι → ℕ)
    (h : (i : ι) → E (arity i)) (g : (i : ι) → F (arity i))
    (hh : ∀ i j, i ≠ j → arity i = arity j → h i ≠ 0 ∨ h j ≠ 0)
    (hg : ∀ i j, i ≠ j → arity i = arity j → g i ≠ 0 ∨ g j ≠ 0) :
    ∃ tag : ι → ℚ, (∀ i, 0 < tag i) ∧
      Function.Injective (fun i => (⟨arity i, (tag i : K) • h i⟩ : (r : ℕ) × E r)) ∧
      Function.Injective (fun i => (⟨arity i, (tag i : K) • g i⟩ : (r : ℕ) × F r)) := by
  obtain ⟨tag, hh', hg'⟩ := exists_common_typed_tags (K := K) arity h g hh hg
  refine ⟨fun i => ((tag i + 1 : ℕ) : ℚ), ?_, ?_⟩
  · intro i
    change (0 : ℚ) < ((tag i + 1 : ℕ) : ℚ)
    exact Nat.cast_pos.mpr (Nat.succ_pos _)
  · simpa only [Rat.cast_natCast] using And.intro hh' hg'
end DependentFamilies

section Search
variable {n : ℕ} {E F : ℕ → Type*}
variable [∀ r, AddCommGroup (E r)] [∀ r, Module K (E r)]
variable [∀ r, AddCommGroup (F r)] [∀ r, Module K (F r)]
variable [∀ r, DecidableEq (E r)] [∀ r, DecidableEq (F r)]

def tagCandidate (n code : ℕ) : Fin n → ℕ :=
  (Encodable.decode (α := Fin n → ℕ) code).getD (fun _ => 0)

@[simp] theorem tagCandidate_encode (tag : Fin n → ℕ) :
    tagCandidate n (Encodable.encode tag) = tag := by
  simp [tagCandidate, Encodable.encodek]

/-- Finite exact equality test for a proposed vector of tags. -/
def tagsAccept (arity : Fin n → ℕ) (h : (i : Fin n) → E (arity i))
    (g : (i : Fin n) → F (arity i)) (code : ℕ) : Bool :=
  decide (
    (∀ i j, (⟨arity i, ((tagCandidate n code i + 1 : ℕ) : K) • h i⟩ : (r : ℕ) × E r) =
      ⟨arity j, ((tagCandidate n code j + 1 : ℕ) : K) • h j⟩ → i = j) ∧
    (∀ i j, (⟨arity i, ((tagCandidate n code i + 1 : ℕ) : K) • g i⟩ : (r : ℕ) × F r) =
      ⟨arity j, ((tagCandidate n code j + 1 : ℕ) : K) • g j⟩ → i = j))

theorem exists_accepted_code (arity : Fin n → ℕ)
    (h : (i : Fin n) → E (arity i)) (g : (i : Fin n) → F (arity i))
    (hh : ∀ i j, i ≠ j → arity i = arity j → h i ≠ 0 ∨ h j ≠ 0)
    (hg : ∀ i j, i ≠ j → arity i = arity j → g i ≠ 0 ∨ g j ≠ 0) :
    ∃ code, tagsAccept (K := K) arity h g code = true := by
  obtain ⟨tag, ht, gt⟩ := exists_common_typed_tags (K := K) arity h g hh hg
  refine ⟨Encodable.encode tag, ?_⟩
  simp only [tagsAccept, tagCandidate_encode, decide_eq_true_eq]
  exact ⟨ht, gt⟩

/-- Total exact search; its termination follows from finite avoidance. The
supplied operations/equality still require an encoded-number implementation
when this API is used as a component of the paper's uniform algorithm. -/
def findTagCode (arity : Fin n → ℕ)
    (h : (i : Fin n) → E (arity i)) (g : (i : Fin n) → F (arity i))
    (hh : ∀ i j, i ≠ j → arity i = arity j → h i ≠ 0 ∨ h j ≠ 0)
    (hg : ∀ i j, i ≠ j → arity i = arity j → g i ≠ 0 ∨ g j ≠ 0) : ℕ :=
  Nat.find (exists_accepted_code (K := K) arity h g hh hg)

theorem findTagCode_spec (arity : Fin n → ℕ)
    (h : (i : Fin n) → E (arity i)) (g : (i : Fin n) → F (arity i))
    (hh : ∀ i j, i ≠ j → arity i = arity j → h i ≠ 0 ∨ h j ≠ 0)
    (hg : ∀ i j, i ≠ j → arity i = arity j → g i ≠ 0 ∨ g j ≠ 0) :
    tagsAccept (K := K) arity h g (findTagCode (K := K) arity h g hh hg) = true :=
  Nat.find_spec (exists_accepted_code (K := K) arity h g hh hg)

def findRationalTags (arity : Fin n → ℕ)
    (h : (i : Fin n) → E (arity i)) (g : (i : Fin n) → F (arity i))
    (hh : ∀ i j, i ≠ j → arity i = arity j → h i ≠ 0 ∨ h j ≠ 0)
    (hg : ∀ i j, i ≠ j → arity i = arity j → g i ≠ 0 ∨ g j ≠ 0) : Fin n → ℚ :=
  fun i => ((tagCandidate n (findTagCode (K := K) arity h g hh hg) i + 1 : ℕ) : ℚ)

theorem findRationalTags_spec (arity : Fin n → ℕ)
    (h : (i : Fin n) → E (arity i)) (g : (i : Fin n) → F (arity i))
    (hh : ∀ i j, i ≠ j → arity i = arity j → h i ≠ 0 ∨ h j ≠ 0)
    (hg : ∀ i j, i ≠ j → arity i = arity j → g i ≠ 0 ∨ g j ≠ 0) :
    let tag := findRationalTags (K := K) arity h g hh hg
    (∀ i, 0 < tag i) ∧
      Function.Injective (fun i => (⟨arity i, (tag i : K) • h i⟩ : (r : ℕ) × E r)) ∧
      Function.Injective (fun i => (⟨arity i, (tag i : K) • g i⟩ : (r : ℕ) × F r)) := by
  dsimp only
  refine ⟨?_, ?_⟩
  · intro i
    exact Nat.cast_pos.mpr (Nat.succ_pos _)
  · have hs := findTagCode_spec (K := K) arity h g hh hg
    simpa only [tagsAccept, decide_eq_true_eq, findRationalTags, Rat.cast_natCast,
      Function.Injective] using hs
end Search
end ComplexCSP.ScalarTags
