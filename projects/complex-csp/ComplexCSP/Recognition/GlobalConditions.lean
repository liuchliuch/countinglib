import ComplexCSP.Algebra.LegalPurificationExistence
import ComplexCSP.Structure.GeneratedBlockOrthogonality

/-! # Literal joint and singleton Block Orthogonality

Finite tuples retain the paper's joint quantifier and distinct-table requirement.
The displayed purification uses the legal printed prime map. Positive normalized
forms have the same BO predicate by the separately proved scaling theorem.
No singleton condition is substituted into the joint definition.
-/
namespace ComplexCSP
open BlockOrthogonality RowTypes GeneratingSet
open Purification.PurificationMap

variable (D : Type) [Fintype D]

/-- A positive-arity table. Its actual arity is `rowArity + 1`. -/
structure PositiveTable where
  rowArity : ℕ
  value : (Fin (rowArity + 1) → D) → ℂ

namespace PositiveTable
variable {D}

noncomputable def rows (T : PositiveTable D) : (Fin T.rowArity → D) → D → ℂ :=
  tableRows T.value

/-- The exact finite set of nonzero complex units appearing in the table. -/
noncomputable def nonzeroValues (T : PositiveTable D) : Finset ℂˣ := by
  classical
  exact Finset.univ.image (fun p : {p : (Fin T.rowArity → D) × D // T.rows p.1 p.2 ≠ 0} =>
    Units.mk0 (T.rows p.val.1 p.val.2) p.property)

@[simp] theorem mem_nonzeroValues (T : PositiveTable D) (u : ℂˣ) :
    u ∈ T.nonzeroValues ↔ ∃ x z, (u : ℂ) = T.rows x z := by
  classical
  simp only [nonzeroValues, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨⟨x,z⟩, hx⟩, he⟩
    exact ⟨x,z,(congrArg Units.val he).symm⟩
  · rintro ⟨x,z,he⟩
    have hz : T.rows x z ≠ 0 := by rw [← he]; exact u.ne_zero
    exact ⟨⟨(x,z),hz⟩, Units.ext he.symm⟩

theorem entryGroup_eq (T : PositiveTable D) :
    entryGroup T.rows = LegalGeneratingSet.EntryGroup T.nonzeroValues := by
  unfold entryGroup LegalGeneratingSet.EntryGroup
  congr 1
  ext u
  exact (T.mem_nonzeroValues u).symm

/-- Legal ambient purification restricted to this table's intrinsic entry group. -/
noncomputable def purifiedRows (T : PositiveTable D) {S : Finset ℂˣ}
    (L : LegalGeneratingSet S) (hTS : T.nonzeroValues ⊆ S) :
    (Fin T.rowArity → D) → D → ℂ :=
  purifyTable T.rows (L.restrictMap (entryGroup T.rows) (by
    rw [T.entryGroup_eq]
    exact Subgroup.closure_mono hTS))

/-- Lemma 3.1's full BO conclusion, now for actual finite tables and arbitrary
legal ambient generating choices rather than abstract assumed maps. -/
theorem ambient_BO_iff (T : PositiveTable D) {S U : Finset ℂˣ}
    (L : LegalGeneratingSet S) (M : LegalGeneratingSet U)
    (hTS : T.nonzeroValues ⊆ S) (hTU : T.nonzeroValues ⊆ U) :
    BlockOrthogonal (T.purifiedRows L hTS) ↔ BlockOrthogonal (T.purifiedRows M hTU) := by
  apply Purification.PurificationMap.blockOrthogonal_iff

noncomputable def singletonRows (T : PositiveTable D) :=
  T.purifiedRows (LegalGeneratingSet.choose T.nonzeroValues) (Finset.Subset.refl _)

end PositiveTable

/-- The finite ambient entries of a genuine finite tuple, including mixed arities. -/
noncomputable def jointValues {h : ℕ} (Ts : Fin h → PositiveTable D) : Finset ℂˣ := by
  classical
  exact Finset.univ.biUnion (fun i => (Ts i).nonzeroValues)

theorem nonzeroValues_subset_joint {h : ℕ} (Ts : Fin h → PositiveTable D) (i : Fin h) :
    (Ts i).nonzeroValues ⊆ jointValues D Ts := by
  classical
  intro u hu
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hu⟩

noncomputable def jointRows {h : ℕ} (Ts : Fin h → PositiveTable D) (i : Fin h) :=
  (Ts i).purifiedRows (LegalGeneratingSet.choose (jointValues D Ts))
    (nonzeroValues_subset_joint D Ts i)

variable {D} {ι : Type} (L : Language D ℂ ι)

/-- Definition 2.2 in its legal printed form: the tuple is nonempty, pairwise
distinct, consists of generated positive-arity tables, and is jointly purified. -/
def JointBO : Prop :=
  ∀ (h : ℕ), 0 < h → ∀ (Ts : Fin h → PositiveTable D),
    Function.Injective Ts → (∀ i, Instance.Generated L (Ts i).value) →
      ∀ i, 0 < (Ts i).rowArity → BlockOrthogonal (jointRows D Ts i)

/-- The independently stated singleton condition, not used in the joint definition. -/
def SingletonBO : Prop :=
  ∀ T : PositiveTable D, Instance.Generated L T.value → 0 < T.rowArity →
    BlockOrthogonal T.singletonRows

/-- Corollary 3.2: actual legal ambient invariance reduces the original joint
condition to singleton purification. -/
theorem jointBO_iff_singletonBO : JointBO L ↔ SingletonBO L := by
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

/-- A one-row matrix is automatically BO, including the zero table. -/
theorem blockOrthogonal_subsingleton_rows {X : Type} [Subsingleton X]
    (G : X → D → ℂ) : BlockOrthogonal G := by
  constructor
  · intro x y hx hy
    have he : y = x := Subsingleton.elim _ _
    subst y
    left
    exact ⟨1, by norm_num, fun z => by simp⟩
  · intro x y hx hy hm
    have he : y = x := Subsingleton.elim _ _
    subst y
    exact Or.inl (proportional_refl _)

/-- Legal singleton purification and the proved coarsening theorem give BO of
all original generated tables. No statement about original BO is assumed. -/
theorem JointBO.original (h : JointBO L) : AllGeneratedOriginalBO L := by
  intro n G hG
  cases n with
  | zero => exact blockOrthogonal_subsingleton_rows (tableRows G)
  | succ n =>
    let T : PositiveTable D := ⟨n + 1, G⟩
    have hp := (jointBO_iff_singletonBO L).mp h T hG (Nat.succ_pos n)
    unfold PositiveTable.singletonRows PositiveTable.purifiedRows at hp
    exact original_blockOrthogonal_of_purified T.rows _ hp

/-- Theorem 7.5's existence endpoint now follows from the literal joint global
condition, through actual support realization, finite repair and compactness. -/
theorem JointBO.common_support_maltsev [Nonempty D] (h : JointBO L) :
    ∃ m : MaltsevRelations.Operation D, MaltsevRelations.IsMaltsev m ∧
      MaltsevRelations.CommonPolymorphism (generatedSupports L) m :=
  common_maltsev_of_allGeneratedOriginalBO (h.original L)

end ComplexCSP
