import ComplexCSP.Recognition.GlobalConditions

/-! # Actual arity compression through legal joint purification

A two-row witness uses at most `|D|²` ordered-pair row coordinates and one
separate final coordinate. All transformations are literal generated minors.
-/
namespace ComplexCSP
open BlockOrthogonality RowTypes GeneratingSet
open Purification.PurificationMap

variable {D : Type} [Fintype D]

/-- One common legal ambient map assigns equal values to equal original entries,
even when they occur in tables with different arities and intrinsic groups. -/
theorem PositiveTable.purified_entry_eq {T U : PositiveTable D} {S : Finset ℂˣ}
    (L : LegalGeneratingSet S) (hT : T.nonzeroValues ⊆ S) (hU : U.nonzeroValues ⊆ S)
    (x : Fin T.rowArity → D) (y : Fin U.rowArity → D) (z w : D)
    (he : T.rows x z = U.rows y w) :
    T.purifiedRows L hT x z = U.purifiedRows L hU y w := by
  classical
  by_cases hz : T.rows x z = 0
  · have hw : U.rows y w = 0 := he.symm.trans hz
    simp [PositiveTable.purifiedRows, purifyTable, encodeTable, hz, hw]
  · have hw : U.rows y w ≠ 0 := by rwa [← he]
    simp only [PositiveTable.purifiedRows, purifyTable, Function.comp_apply,
      encodeTable, dif_neg hz, dif_neg hw, Purification.PurificationMap.entry_some]
    apply congrArg (fun q : LegalGeneratingSet.EntryGroup S => (L.purifiedHom q : ℂ))
    apply Subtype.ext
    exact Units.ext he

noncomputable def pairIndex : D × D ≃ Fin (Fintype.card (D × D)) := Fintype.equivFin _

noncomputable def compressScope {n : ℕ} (x y : Fin n → D) :
    Fin (n + 1) → Fin (Fintype.card (D × D) + 1) :=
  Fin.lastCases (Fin.last _) (fun i => (pairIndex (x i,y i)).castSucc)

noncomputable def PositiveTable.compress (T : PositiveTable D)
    (x y : Fin T.rowArity → D) : PositiveTable D where
  rowArity := Fintype.card (D × D)
  value a := T.value (a ∘ compressScope x y)

noncomputable def compressedFirst : Fin (Fintype.card (D × D)) → D :=
  fun i => (pairIndex.symm i).1
noncomputable def compressedSecond : Fin (Fintype.card (D × D)) → D :=
  fun i => (pairIndex.symm i).2

@[simp] theorem PositiveTable.compress_first (T : PositiveTable D)
    (x y : Fin T.rowArity → D) (z : D) :
    (T.compress x y).rows compressedFirst z = T.rows x z := by
  change T.value (Fin.snoc compressedFirst z ∘ compressScope x y) = T.value (Fin.snoc x z)
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [compressScope]
  · simp [compressScope, compressedFirst]

@[simp] theorem PositiveTable.compress_second (T : PositiveTable D)
    (x y : Fin T.rowArity → D) (z : D) :
    (T.compress x y).rows compressedSecond z = T.rows y z := by
  change T.value (Fin.snoc compressedSecond z ∘ compressScope x y) = T.value (Fin.snoc y z)
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [compressScope]
  · simp [compressScope, compressedSecond]

/-- Every row of the compressed table is an actual row of the source table. -/
theorem PositiveTable.compress_row (T : PositiveTable D)
    (x y : Fin T.rowArity → D) (a : Fin (Fintype.card (D × D)) → D) (z : D) :
    (T.compress x y).rows a z = T.rows (fun i => a (pairIndex (x i,y i))) z := by
  change T.value (Fin.snoc a z ∘ compressScope x y) =
    T.value (Fin.snoc (fun i => a (pairIndex (x i,y i))) z)
  congr 1
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [compressScope]

theorem PositiveTable.compress_values_subset (T : PositiveTable D)
    (x y : Fin T.rowArity → D) : (T.compress x y).nonzeroValues ⊆ T.nonzeroValues := by
  intro u hu
  obtain ⟨a,z,he⟩ := ((T.compress x y).mem_nonzeroValues u).mp hu
  exact (T.mem_nonzeroValues u).mpr
    ⟨(fun i => a (pairIndex (x i,y i))),z,he.trans (T.compress_row x y a z)⟩

variable {ι : Type} (L : Language D ℂ ι)

/-- Singleton BO tested only up to the explicit external arity bound. -/
def BoundedSingletonBO : Prop :=
  ∀ T : PositiveTable D, Instance.Generated L T.value →
    0 < T.rowArity → T.rowArity + 1 ≤ Fintype.card D ^ 2 + 1 →
      BlockOrthogonal T.singletonRows

/-- The full arity-compression equivalence, using arbitrary legal ambient
invariance to preserve the two relevant purified rows. -/
theorem singletonBO_iff_bounded [Nonempty D] : SingletonBO L ↔ BoundedSingletonBO L := by
  constructor
  · intro h T hT hpos hbound
    exact h T hT hpos
  · intro h T hT hpos
    have hpairs (x y : Fin T.rowArity → D) :
        ∃ Q : (Fin (Fintype.card (D × D)) → D) → D → ℂ,
          BlockOrthogonal Q ∧ Q compressedFirst = T.singletonRows x ∧
            Q compressedSecond = T.singletonRows y := by
      let U := T.compress x y
      have hU : Instance.Generated L U.value := Instance.generated_diagonal_minor hT (compressScope x y)
      have hposU : 0 < U.rowArity := Fintype.card_pos
      have hboundU : U.rowArity + 1 ≤ Fintype.card D ^ 2 + 1 := by simp [U, PositiveTable.compress, pow_two]
      have hBU := h U hU hposU hboundU
      let P := LegalGeneratingSet.choose T.nonzeroValues
      have hUS : U.nonzeroValues ⊆ T.nonzeroValues := T.compress_values_subset x y
      have hBQ : BlockOrthogonal (U.purifiedRows P hUS) :=
        (U.ambient_BO_iff P (LegalGeneratingSet.choose U.nonzeroValues)
          hUS (Finset.Subset.refl _)).mpr hBU
      refine ⟨U.purifiedRows P hUS,hBQ,?_,?_⟩
      · funext z
        exact PositiveTable.purified_entry_eq P hUS (Finset.Subset.refl _) _ _ z z
          (T.compress_first x y z)
      · funext z
        exact PositiveTable.purified_entry_eq P hUS (Finset.Subset.refl _) _ _ z z
          (T.compress_second x y z)
    constructor
    · intro x y hx hy
      obtain ⟨Q,hQ,hxQ,hyQ⟩ := hpairs x y
      simp only [← hxQ, ← hyQ] at hx hy ⊢
      exact hQ.1 _ _ hx hy
    · intro x y hx hy hm
      obtain ⟨Q,hQ,hxQ,hyQ⟩ := hpairs x y
      simp only [← hxQ, ← hyQ] at hx hy hm ⊢
      exact hQ.2 _ _ hx hy hm

/-- Global joint BO is equivalent to its finite external-arity range. The
presenting instance sizes and hidden-variable counts remain unbounded. -/
theorem jointBO_iff_bounded [Nonempty D] : JointBO L ↔ BoundedSingletonBO L :=
  (jointBO_iff_singletonBO L).trans (singletonBO_iff_bounded L)

/-- Lemma 3.4 in exact positive-arity generated-table semantics. This is an
external-arity bound only, not a bound on counterexample instance size. -/
theorem bounded_external_arity_counterexample [Nonempty D] (h : ¬ SingletonBO L) :
    ∃ T : PositiveTable D, Instance.Generated L T.value ∧ 0 < T.rowArity ∧
      T.rowArity + 1 ≤ Fintype.card D ^ 2 + 1 ∧ ¬ BlockOrthogonal T.singletonRows := by
  classical
  have hn : ¬ BoundedSingletonBO L := fun hb => h ((singletonBO_iff_bounded L).mpr hb)
  unfold BoundedSingletonBO at hn
  push_neg at hn
  exact hn

end ComplexCSP
