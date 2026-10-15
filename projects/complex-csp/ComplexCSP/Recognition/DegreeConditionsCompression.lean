import ComplexCSP.Recognition.DegreeConditions
import ComplexCSP.Structure.BoundedArity

/-! # External-arity compression inside the degree-multiple family

Every compressed witness is an actual degree-preserving boundary identification.
Legal ambient purification preserves the two witness rows exactly as in the
ordinary proof, without using unrestricted joint BO.
-/
namespace ComplexCSP
open BlockOrthogonality RowTypes GeneratingSet
variable {D ι : Type} [Fintype D] (L : Language D ℂ ι) (δ : ℕ)

/-- Singleton BO tested only up to the explicit external arity bound. -/
def DegreeBoundedSingletonBO : Prop :=
  ∀ T : PositiveTable D, DegreeGenerated L δ T.value →
    0 < T.rowArity → T.rowArity + 1 ≤ Fintype.card D ^ 2 + 1 →
      BlockOrthogonal T.singletonRows

/-- The full arity-compression equivalence, using arbitrary legal ambient
invariance to preserve the two relevant purified rows. -/
theorem degreeSingletonBO_iff_bounded [Nonempty D] : DegreeSingletonBO L δ ↔ DegreeBoundedSingletonBO L δ := by
  constructor
  · intro h T hT hpos hbound
    exact h T hT hpos
  · intro h T hT hpos
    have hpairs (x y : Fin T.rowArity → D) :
        ∃ Q : (Fin (Fintype.card (D × D)) → D) → D → ℂ,
          BlockOrthogonal Q ∧ Q compressedFirst = T.singletonRows x ∧
            Q compressedSecond = T.singletonRows y := by
      let U := T.compress x y
      have hU : DegreeGenerated L δ U.value := DegreeGenerated.diagonal_minor hT (compressScope x y)
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
theorem degreeJointBO_iff_bounded [Nonempty D] : DegreeJointBO L δ ↔ DegreeBoundedSingletonBO L δ :=
  (degreeJointBO_iff_singletonBO L δ).trans (degreeSingletonBO_iff_bounded L δ)

/-- Lemma 3.4 in exact positive-arity generated-table semantics. This is an
external-arity bound only, not a bound on counterexample instance size. -/
theorem degree_bounded_external_arity_counterexample [Nonempty D] (h : ¬ DegreeSingletonBO L δ) :
    ∃ T : PositiveTable D, DegreeGenerated L δ T.value ∧ 0 < T.rowArity ∧
      T.rowArity + 1 ≤ Fintype.card D ^ 2 + 1 ∧ ¬ BlockOrthogonal T.singletonRows := by
  classical
  have hn : ¬ DegreeBoundedSingletonBO L δ := fun hb => h ((degreeSingletonBO_iff_bounded L δ).mpr hb)
  unfold DegreeBoundedSingletonBO at hn
  push_neg at hn
  exact hn

end ComplexCSP
