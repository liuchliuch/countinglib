import ComplexCSP.Complexity.PhaseObstruction
import ComplexCSP.Complexity.ObstructionWitness

/-! # Literal non-BO reduces to a finite nonnegative Gram obstruction

This endpoint derives the finite generated witness, actual legal purification,
phase exponent, all zero-support handling, a common algebraic number field,
finite matrix indices, and the genuine charged oracle reduction. It assumes no
Bulatov–Grohe hardness theorem. The resulting explicit Gram witness is the input
to that remaining independent counting-hardness prerequisite.
-/
namespace ComplexCSP.ComplexityNonBOToGram
open ComplexityReducedGram BlockOrthogonality
variable {D : Type} [Fintype D] {s : ℕ}

theorem exists_reduced_gram (L : Language D ℂ (Fin s))
    (hL : ∀ i a,IsAlgebraic ℚ (L.value i a)) (hnot : ¬JointBO L) :
    Nonempty (Witness L) := by
  classical
  obtain ⟨T,P,hP,hr,hBO⟩ := ComplexityObstructionWitness.finite_witness_of_not_joint L hnot
  have hrows : (LegalSingletonPurification.choice T).purifyTable T.rows
      (LegalSingletonPurification.contains_rows T)=T.singletonRows := rfl
  have hnot' : ¬BlockOrthogonal ((LegalSingletonPurification.choice T).purifyTable T.rows
      (LegalSingletonPurification.contains_rows T)) := by rwa [hrows]
  obtain ⟨K,hK,heven,hbad | ⟨t,ht,htb,hbad⟩⟩ :=
    PhaseLegalObstruction.legal_unscaled_obstruction (LegalSingletonPurification.choice T)
      T.rows (LegalSingletonPurification.contains_rows T) hnot'
  · refine ⟨ComplexityMagnitudeObstruction.witness L hL T P hP hr ?_⟩
    simpa only [hrows,←LegalSingletonPurification.rows_value T] using hbad 
  · refine ⟨ComplexityPhaseObstruction.witness L hL T P hP hr 1 (t*K-1) ?_⟩
    have he : GramPowerGadget.matrix (LegalSingletonPurification.value T) 1 (t*K-1) =
        (fun x y => PhasePowerAlgebra.powerPair
          ((LegalSingletonPurification.choice T).purifyTable T.rows
            (LegalSingletonPurification.contains_rows T) x)
          ((LegalSingletonPurification.choice T).purifyTable T.rows
            (LegalSingletonPurification.contains_rows T) y) (t*K)) := by
      rw [hrows,←LegalSingletonPurification.rows_value T]
      funext x y
      simp only [GramPowerGadget.matrix,GramGadget.row,PhasePowerAlgebra.powerPair,
        RowTypes.tableRows,pow_one]
    rwa [he]

/-- The already proved structural equivalence feeds the same actual reduction.
This theorem still does not assert #P-hardness until the explicit Gram
obstruction hardness prerequisite is proved separately. -/
theorem exists_reduced_gram_of_not_conditions [Nonempty D]
    (L : Language D ℂ (Fin s)) (hL : ∀ i a,IsAlgebraic ℚ (L.value i a))
    (hnot : ¬CaiChenConditions L) : Nonempty (Witness L) :=
  exists_reduced_gram L hL (fun hb => hnot ((structural_collapse L hL).mpr hb))

end ComplexCSP.ComplexityNonBOToGram
