import ComplexCSP.Algebra.LegalPurificationNormalization

/-!
# Legal ambient purification of literal complex tables

`ContainsTable` is exactly containment of every nonzero table entry in the finite
ambient value set. It yields the intrinsic-subgroup inclusion, constructs the
entrywise purification of the actual table, and connects the arbitrary-legal
ambient theorem and purity normalization without a supplied option encoding.
-/
namespace ComplexCSP.GeneratingSet

open Purification
open BlockOrthogonality

namespace LegalGeneratingSet

variable {X D : Type*} {S T : Finset ℂˣ}

/-- A finite ambient value set contains all nonzero entries of this table. -/
def ContainsTable (S : Finset ℂˣ) (G : X → D → ℂ) : Prop :=
  ∀ x z (h : G x z ≠ 0), Units.mk0 (G x z) h ∈ S

theorem intrinsic_le_ambient (G : X → D → ℂ) (h : ContainsTable S G) :
    PurificationMap.entryGroup G ≤ EntryGroup S := by
  apply (Subgroup.closure_le _).mpr
  intro u hu
  obtain ⟨x, z, hux⟩ := hu
  have hx : G x z ≠ 0 := by rw [← hux]; exact Units.ne_zero u
  have heq : Units.mk0 (G x z) hx = u := Units.ext hux.symm
  apply Subgroup.subset_closure
  rw [← heq]
  exact h x z hx

/-- The structural map on the actual intrinsic table group, derived from the
arbitrary ambient legal choice. -/
noncomputable def tableMap (L : LegalGeneratingSet S) (G : X → D → ℂ)
    (h : ContainsTable S G) :
    PurificationMap (PurificationMap.entryGroup G) (PurificationMap.entryGroup G).subtype :=
  L.restrictMap _ (intrinsic_le_ambient G h)

/-- The literal entrywise printed purification of a complex table. -/
noncomputable def purifyTable (L : LegalGeneratingSet S) (G : X → D → ℂ)
    (h : ContainsTable S G) : X → D → ℂ :=
  PurificationMap.purifyTable G (L.tableMap G h)

@[simp] theorem purifyTable_zero (L : LegalGeneratingSet S) (G : X → D → ℂ)
    (h : ContainsTable S G) (x : X) (z : D) (hz : G x z = 0) :
    L.purifyTable G h x z = 0 := by
  classical
  simp [purifyTable, PurificationMap.purifyTable, PurificationMap.encodeTable, hz]

theorem purifyTable_nonzero (L : LegalGeneratingSet S) (G : X → D → ℂ)
    (h : ContainsTable S G) (x : X) (z : D) (hz : G x z ≠ 0) :
    L.purifyTable G h x z =
      (L.purifiedHom ⟨Units.mk0 (G x z) hz, Subgroup.subset_closure (h x z hz)⟩ : ℂ) := by
  classical
  simp only [purifyTable, PurificationMap.purifyTable, Function.comp_apply,
    PurificationMap.encodeTable, dif_neg hz, PurificationMap.entry_some]
  rfl

theorem purifyTable_eq_zero_iff (L : LegalGeneratingSet S) (G : X → D → ℂ)
    (h : ContainsTable S G) (x : X) (z : D) :
    L.purifyTable G h x z = 0 ↔ G x z = 0 := by
  by_cases hz : G x z = 0
  · simp [hz]
  · rw [L.purifyTable_nonzero G h x z hz]
    simp [hz, Units.ne_zero]

/-- Actual ambient invariance, with both finite ambient sets and both legal
choices explicit and potentially different. -/
theorem table_ambient_blockOrthogonal_iff [Fintype D]
    (L : LegalGeneratingSet S) (M : LegalGeneratingSet T) (G : X → D → ℂ)
    (hS : ContainsTable S G) (hT : ContainsTable T G) :
    BlockOrthogonal (L.purifyTable G hS) ↔ BlockOrthogonal (M.purifyTable G hT) :=
  (L.tableMap G hS).blockOrthogonal_iff (M.tableMap G hT) (PurificationMap.encodeTable G)

/-- The exact same ambient result after positive table-wide normalization. -/
theorem table_normalized_ambient_blockOrthogonal_iff [Fintype D]
    (L : LegalGeneratingSet S) (M : LegalGeneratingSet T) (G : X → D → ℂ)
    (hS : ContainsTable S G) (hT : ContainsTable T G)
    {N K : ℝ} (hN : 0 < N) (hK : 0 < K) :
    BlockOrthogonal (fun x z => (N : ℂ) * L.purifyTable G hS x z) ↔
      BlockOrthogonal (fun x z => (K : ℂ) * M.purifyTable G hT x z) := by
  rw [blockOrthogonal_positive_scale_iff hN, blockOrthogonal_positive_scale_iff hK]
  exact L.table_ambient_blockOrthogonal_iff M G hS hT

/-- The original-table corollary used for generated powers in Section 8. -/
theorem original_blockOrthogonal [Fintype D] (L : LegalGeneratingSet S)
    (G : X → D → ℂ) (h : ContainsTable S G)
    (hBO : BlockOrthogonal (L.purifyTable G h)) : BlockOrthogonal G :=
  PurificationMap.original_blockOrthogonal_of_purified G (L.tableMap G h) hBO

/-- Literal actual tables admit a positive natural normalization whose every
entry is pure; zero entries are retained exactly. -/
theorem table_exists_pure_normalization (L : LegalGeneratingSet S)
    (G : X → D → ℂ) (h : ContainsTable S G) :
    ∃ N : ℕ, 0 < N ∧ ∀ x z, IsPureValue ((N : ℂ) * L.purifyTable G h x z) := by
  obtain ⟨N, hN, hP⟩ := L.exists_pure_normalization
  refine ⟨N, hN, ?_⟩
  intro x z
  by_cases hz : G x z = 0
  · rw [L.purifyTable_zero G h x z hz, mul_zero]
    exact zero_isPureValue
  · rw [L.purifyTable_nonzero G h x z hz]
    exact hP ⟨Units.mk0 (G x z) hz, h x z hz⟩

end LegalGeneratingSet
end ComplexCSP.GeneratingSet
