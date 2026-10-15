import ComplexCSP.Structure.StructuralCollapse
import ComplexCSP.Instances.PresentationAlgorithms

/-! # Exact finite witnesses and the two non-BO hardness branches

This extracts actual finite presentations from the literal joint condition.
It does not assume or assert the unresolved homomorphism hardness theorem.
-/
namespace ComplexCSP.ComplexityObstructionWitness
open BlockOrthogonality RowTypes
variable {D ι : Type} [Fintype D] (L : Language D ℂ ι)

/-- Ambient invariance reduces failure of the literal joint quantifier to one
actual generated table with its legally constructed singleton purification. -/
theorem finite_witness_of_not_joint (h : ¬JointBO L) :
    ∃ T : PositiveTable D, ∃ P : Presentation L (Fin (T.rowArity+1)),
      P.table = T.value ∧ 0 < T.rowArity ∧ ¬BlockOrthogonal T.singletonRows := by
  classical
  have hs : ¬SingletonBO L := fun hs => h ((jointBO_iff_singletonBO L).mpr hs)
  unfold SingletonBO at hs
  push_neg at hs
  obtain ⟨T,hT,hpos,hnot⟩ := hs
  obtain ⟨m,I,hI⟩ := hT
  exact ⟨T,⟨m,I⟩,funext hI,hpos,hnot⟩

/-- The project's proved structural collapse removes the need for separate
Type-Partition and Mal'tsev-failure hardness reductions in this proof route. -/
theorem finite_witness_of_not_conditions [Nonempty D] [Fintype ι]
    (hAlg : ∀ i a, IsAlgebraic ℚ (L.value i a)) (h : ¬CaiChenConditions L) :
    ∃ T : PositiveTable D, ∃ P : Presentation L (Fin (T.rowArity+1)),
      P.table = T.value ∧ 0 < T.rowArity ∧ ¬BlockOrthogonal T.singletonRows :=
  finite_witness_of_not_joint L (fun hb => h ((structural_collapse L hAlg).mpr hb))

/-- Magnitude-rank failure and phase failure are explicitly separate. The latter
includes an actual nonzero magnitude block sum, not just global nonorthogonality. -/
theorem nonBO_cases {X : Type} (G : X → D → ℂ) (h : ¬BlockOrthogonal G) :
    (¬BlockRankOne G) ∨ (BlockRankOne G ∧ ∃ x y,
      G x ≠ 0 ∧ G y ≠ 0 ∧ MagnitudeProportional (G x) (G y) ∧
      ¬Proportional (G x) (G y) ∧ ∃ z, G x z ≠ 0 ∧
        hermitianSum (G x) (G y) (magnitudeBlock (G x) z) ≠ 0) := by
  classical
  by_cases hr : BlockRankOne G
  · right
    refine ⟨hr,?_⟩
    have hn : ¬∀ x y, G x ≠ 0 → G y ≠ 0 → MagnitudeProportional (G x) (G y) →
        Proportional (G x) (G y) ∨ VectorBlockOrthogonal (G x) (G y) :=
      fun hh => h ⟨hr,hh⟩
    push_neg at hn
    obtain ⟨x,y,hx,hy,hm,hp,hb⟩ := hn
    unfold VectorBlockOrthogonal at hb
    push_neg at hb
    exact ⟨x,y,hx,hy,hm,hp,hb⟩
  · exact Or.inl hr

end ComplexCSP.ComplexityObstructionWitness
