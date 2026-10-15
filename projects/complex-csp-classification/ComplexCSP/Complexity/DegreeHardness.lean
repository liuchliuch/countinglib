import ComplexCSP.Complexity.DegreeHardnessCore
import ComplexCSP.Algebra.NonnegativeGramHardness

/-! # Closed degree-restricted counting hardness in any supplied exact field

This is the hard implication needed by the external consequence of Corollary
1.2. All degree witnesses, legal singleton purifications, source hardness and
fresh-variable degree-preserving substitutions are derived, not assumed.
-/
noncomputable section
open Classical
namespace ComplexCSP.ComplexityDegreeHardness
open PlanarHom PlanarHom.Complexity
variable {D K : Type} [Fintype D] [Field K] [Algebra ℚ K] {s d : ℕ}

/-- Strong internal modulus-unrestricted form; the public paper-facing form
below explicitly retains the positive-modulus hypothesis. -/
theorem hard_of_not_degreeJointBO_any (basis : Module.Basis (Fin d) ℚ K)
    (σ : K →+* ℂ) (M : Language D K (Fin s)) (δ : ℕ)
    (hnot : ¬DegreeJointBO (M.mapValues σ) δ) :
    PromisedSharpPHard (ComplexityGadgetSubstitution.degreePartitionProblem M basis δ) :=
  ComplexityDegreeHardnessCore.hard_of_not_degreeJointBO_of_potts basis σ M δ
    AlgebraicProductInterpolation.RealLanguage.positivePottsFoundation hnot

/-- The literal δ>0 degree-restricted hard implication. -/
theorem hard_of_not_degreeJointBO (basis : Module.Basis (Fin d) ℚ K)
    (σ : K →+* ℂ) (M : Language D K (Fin s)) (δ : ℕ) (_hδ : 0<δ)
    (hnot : ¬DegreeJointBO (M.mapValues σ) δ) :
    PromisedSharpPHard (ComplexityGadgetSubstitution.degreePartitionProblem M basis δ) :=
  hard_of_not_degreeJointBO_any basis σ M δ hnot

/-- Failure of any of the literal degree-restricted Cai–Chen conditions feeds
the same real charged reduction in the supplied coefficient representation. -/
theorem hard_of_not_degreeConditions [Nonempty D] (basis : Module.Basis (Fin d) ℚ K)
    (σ : K →+* ℂ) (M : Language D K (Fin s)) (δ : ℕ) (hδ : 0<δ)
    (hnot : ¬DegreeCaiChenConditions (M.mapValues σ) δ) :
    PromisedSharpPHard (ComplexityGadgetSubstitution.degreePartitionProblem M basis δ) := by
  apply hard_of_not_degreeJointBO basis σ M δ hδ
  intro hbo
  exact hnot ((degree_structural_collapse (M.mapValues σ) δ
    (ComplexityNonBOHardnessCore.realization_algebraic basis σ M)).mpr hbo)

end ComplexCSP.ComplexityDegreeHardness
