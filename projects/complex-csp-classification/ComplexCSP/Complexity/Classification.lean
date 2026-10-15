import ComplexCSP.Complexity.PositiveFP
import ComplexCSP.Complexity.NonBOHardness
import ComplexCSP.Complexity.DegreeHardness

/-! # Closed ordinary and degree complexity dichotomy implications

Each positive branch invokes the actual bounded fixed-language evaluator;
each negative branch invokes the actual charged counting-hardness reduction.
The structural cases are exclusive, but no separation of FP and #P-hardness is
assumed or concluded. Complex-valued partition outputs are not asserted to be
natural-valued #P members.
-/
noncomputable section
namespace ComplexCSP.ComplexityClassification
open PlanarHom PlanarHom.Complexity
variable {D K : Type} [Fintype D] [Field K] [DecidableEq K] [Algebra ℚ K]
variable {s dimension : ℕ} (L : Language D K (Fin s))
variable (basis : Module.Basis (Fin dimension) ℚ K) (σ : K →+* ℂ)

theorem ordinary_jointBO :
    (JointBO (L.mapValues σ) → (ComplexityCSPCountReduction.partitionProblem L basis).InFP) ∧
    (¬JointBO (L.mapValues σ) → PromisedSharpPHard (ComplexityCSPCountReduction.partitionProblem L basis)) :=
  ⟨ComplexityPositiveFP.jointBO_inFP L basis σ,
    ComplexityNonBOHardness.hard_of_not_jointBO basis σ L⟩

theorem degree_jointBO (δ : ℕ) (hδ : 0<δ) :
    (DegreeJointBO (L.mapValues σ) δ → (ComplexityGadgetSubstitution.degreePartitionProblem L basis δ).InFP) ∧
    (¬DegreeJointBO (L.mapValues σ) δ → PromisedSharpPHard (ComplexityGadgetSubstitution.degreePartitionProblem L basis δ)) :=
  ⟨ComplexityPositiveFP.degreeJointBO_inFP L basis σ hδ,
    ComplexityDegreeHardness.hard_of_not_degreeJointBO basis σ L δ hδ⟩

variable [Nonempty D]

theorem ordinary_conditions :
    (CaiChenConditions (L.mapValues σ) → (ComplexityCSPCountReduction.partitionProblem L basis).InFP) ∧
    (¬CaiChenConditions (L.mapValues σ) → PromisedSharpPHard (ComplexityCSPCountReduction.partitionProblem L basis)) :=
  ⟨ComplexityPositiveFP.conditions_inFP L basis σ,
    ComplexityNonBOHardness.hard_of_not_conditions basis σ L⟩

theorem degree_conditions (δ : ℕ) (hδ : 0<δ) :
    (DegreeCaiChenConditions (L.mapValues σ) δ → (ComplexityGadgetSubstitution.degreePartitionProblem L basis δ).InFP) ∧
    (¬DegreeCaiChenConditions (L.mapValues σ) δ → PromisedSharpPHard (ComplexityGadgetSubstitution.degreePartitionProblem L basis δ)) :=
  ⟨ComplexityPositiveFP.degreeConditions_inFP L basis σ hδ,
    ComplexityDegreeHardness.hard_of_not_degreeConditions basis σ L δ hδ⟩

end ComplexCSP.ComplexityClassification
