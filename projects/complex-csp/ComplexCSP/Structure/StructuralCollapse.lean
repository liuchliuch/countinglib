import ComplexCSP.Structure.RowEquivalenceRealization

/-! # Global Type Partition, a common Mal'tsev operation, and structural collapse

The predicates quantify the unbounded ordered generated family. One operation
preserves every generated support and original row relation. The detector uses
a constructive bounded power-sum argument; AlgebraicPowerSumZeros separately
proves the full numbered Lemma 8.3. -/
namespace ComplexCSP
open MaltsevRelations RowTypes

variable {D ι : Type} [Fintype D] (L : Language D ℂ ι)

/-- Definition 2.3's Type Partition condition, including the stipulated empty
prefix convention (which adds no restriction). Row classes use original values. -/
def GlobalTypePartition : Prop :=
  ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n + 1) → D) → ℂ), PaperGenerated L G →
    ∀ (ℓ : ℕ) (hℓ : ℓ ≤ n) (α β : Fin ℓ → D),
      prefixType G hℓ α = prefixType G hℓ β ∨
        Disjoint (prefixType G hℓ α) (prefixType G hℓ β)

/-- The common operation is quantified before all generated supports and row
equivalence relations, exactly as required in the source. -/
def GlobalMaltsev : Prop :=
  ∃ m : Operation D, IsMaltsev m ∧
    (∀ T : PositiveTable D, PaperGenerated L T.value →
      Preserves m {a | T.value a ≠ 0}) ∧
    ∀ (n : ℕ), 0 < n → ∀ (G : (Fin (n + 1) → D) → ℂ),
      PaperGenerated L G → Preserves m (omegaRelation G).tuples

/-- The original three-condition conjunction. -/
def CaiChenConditions : Prop := JointBO L ∧ GlobalTypePartition L ∧ GlobalMaltsev L

theorem JointBO.global_type_partition [Nonempty D] [Fintype ι]
    (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a)) (hBO : JointBO L) :
    GlobalTypePartition L := by
  intro n hn G hG ℓ hℓ α β
  exact RowEquivalenceRealization.generated_type_partition L hAlg hBO hn G
    ((generated_iff_paperGenerated _).mpr hG) hℓ α β

theorem JointBO.global_maltsev [Nonempty D] [Fintype ι]
    (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a)) (hBO : JointBO L) :
    GlobalMaltsev L := by
  obtain ⟨m,hm,hsupp,hrow⟩ :=
    RowEquivalenceRealization.common_support_and_row_maltsev L hAlg hBO
  refine ⟨m,hm,?_,?_⟩
  · intro T hT
    let R : Relation D := ⟨T.rowArity + 1,{a | T.value a ≠ 0}⟩
    exact hsupp R ⟨T.value,(generated_iff_paperGenerated _).mpr hT,rfl⟩
  · intro n hn G hG
    exact hrow n hn G ((generated_iff_paperGenerated _).mpr hG)

/-- Theorem 9.2, with the actual joint BO definition, actual original row types,
and one operation simultaneously preserving the full generated relation family.
This is independent of the disputed isomorphism theorem used by the algorithm. -/
theorem structural_collapse [Nonempty D] [Fintype ι]
    (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a)) :
    CaiChenConditions L ↔ JointBO L := by
  constructor
  · exact And.left
  · intro hBO
    exact ⟨hBO,hBO.global_type_partition L hAlg,hBO.global_maltsev L hAlg⟩

end ComplexCSP
