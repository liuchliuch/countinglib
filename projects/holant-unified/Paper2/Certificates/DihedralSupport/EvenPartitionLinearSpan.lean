module
public import Paper2.Certificates.DihedralSupport.EvenPartitionCoverage
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Tactic.FinCases

/-! The literal F₂ span of the indicators of disjoint blocks is exactly the
set of indicators of unions of selected blocks.  This identifies the source's
linear span with its finite subset-union representation; no accepted-mask
enumeration occurs in this argument. -/
@[expose] public section
namespace Paper2.Certificates.DihedralSupport
open scoped BigOperators

def wordVector (x : Fin 6 → Bool) : Fin 6 → ZMod 2 :=
  fun k => if x k then 1 else 0

def blockIndicator (b : Finset (Fin 6)) : Fin 6 → ZMod 2 :=
  fun k => if k ∈ b then 1 else 0

def blockLinearSpan (B : Finset (Finset (Fin 6))) :
    Submodule (ZMod 2) (Fin 6 → ZMod 2) :=
  Submodule.span (ZMod 2) (blockIndicator '' (B : Set (Finset (Fin 6))))

theorem wordVector_injective : Function.Injective wordVector := by
  intro x y h
  funext k
  have hk := congrFun h k
  cases hx : x k <;> cases hy : y k <;> simp_all [wordVector]

@[simp] theorem wordVector_indicator (b : Finset (Fin 6)) :
    wordVector (fun k => decide (k ∈ b)) = blockIndicator b := by
  funext k
  simp [wordVector,blockIndicator]

private theorem scalar_zero_or_one (a : ZMod 2) : a=0 ∨ a=1 := by
  fin_cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A sum of disjoint block indicators has no overlaps to cancel in F₂. -/
theorem sum_blockIndicator (C : Finset (Finset (Fin 6)))
    (hd : (C : Set (Finset (Fin 6))).PairwiseDisjoint id) :
    (∑ b ∈ C, blockIndicator b) = blockIndicator (C.biUnion id) := by
  classical
  funext k
  simp only [Finset.sum_apply]
  by_cases hk : k ∈ C.biUnion id
  · obtain ⟨b,hb,hkb⟩ := Finset.mem_biUnion.mp hk
    change k ∈ b at hkb
    rw [Finset.sum_eq_single b]
    · simp [blockIndicator,hkb,hk]
    · intro c hc hcb
      have hkc : k ∉ c := by
        intro hkc
        exact (Finset.disjoint_left.mp (hd hc hb hcb)) hkc hkb
      simp [blockIndicator,hkc]
    · simp [hb]
  · have hn : ∀ b ∈ C, k ∉ b := by
      intro b hb hkb
      exact hk (Finset.mem_biUnion.mpr ⟨b,hb,hkb⟩)
    rw [show blockIndicator (C.biUnion id) k=0 by simp [blockIndicator,hk]]
    apply Finset.sum_eq_zero
    intro b hb
    simp [blockIndicator,hn b hb]

/-- The coefficients of any F₂ linear combination select precisely the
blocks whose coefficient is one. -/
theorem coefficient_sum (B : Finset (Finset (Fin 6)))
    (a : Finset (Fin 6) → ZMod 2) :
    (∑ b ∈ B, a b • blockIndicator b) =
      ∑ b ∈ B.filter (fun b => a b=1), blockIndicator b := by
  classical
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro b hb
  rcases scalar_zero_or_one (a b) with h | h <;> simp [h]

/-- Exact finite-combination semantics of the actual `Submodule.span`.
Only disjointness is needed; the even/covering/nonempty partition clauses
are used elsewhere in the source classification. -/
theorem mem_blockLinearSpan_iff (B : Finset (Finset (Fin 6)))
    (hd : (B : Set (Finset (Fin 6))).PairwiseDisjoint id)
    (v : Fin 6 → ZMod 2) :
    v ∈ blockLinearSpan B ↔
      ∃ C : Finset (Finset (Fin 6)), C ⊆ B ∧ v=blockIndicator (C.biUnion id) := by
  classical
  constructor
  · intro hv
    obtain ⟨a,ha⟩ :=
      (Submodule.mem_span_image_finset_iff_exists_fun' (ZMod 2)).mp hv
    let C := B.filter (fun b => a b=1)
    have hCB : C ⊆ B := Finset.filter_subset _ _
    have hdC : (C : Set (Finset (Fin 6))).PairwiseDisjoint id := by
      intro b hb c hc hbc
      exact hd (hCB hb) (hCB hc) hbc
    refine ⟨C,hCB,?_⟩
    rw [←ha,coefficient_sum]
    exact sum_blockIndicator C hdC
  · rintro ⟨C,hCB,rfl⟩
    rw [←sum_blockIndicator C (by
      intro b hb c hc hbc
      exact hd (hCB hb) (hCB hc) hbc)]
    apply Submodule.sum_mem
    intro b hb
    exact Submodule.subset_span ⟨b,hCB hb,rfl⟩

/-- Boolean membership in the literal F₂ span, with the selected subset
written explicitly so that the finite coset layer needs no extra choice. -/
theorem wordVector_mem_blockLinearSpan_exists
    (B : Finset (Finset (Fin 6))) (h : EvenPartition B) (x : Fin 6 → Bool) :
    wordVector x ∈ blockLinearSpan B ↔
      ∃ C : Finset (Finset (Fin 6)), C ⊆ B ∧
        x=(fun k => decide (k ∈ C.biUnion id)) := by
  rw [mem_blockLinearSpan_iff B h.2.2.1]
  constructor
  · rintro ⟨C,hCB,hx⟩
    exact ⟨C,hCB,wordVector_injective (hx.trans (wordVector_indicator _).symm)⟩
  · rintro ⟨C,hCB,rfl⟩
    exact ⟨C,hCB,wordVector_indicator _⟩

end Paper2.Certificates.DihedralSupport

