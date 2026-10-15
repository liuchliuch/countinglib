import ComplexCSP.Complexity.NonBOHardnessCore
import ComplexCSP.Algebra.DegreeObstructionWitness
import ComplexCSP.Complexity.GadgetSubstitutionReduction
import ComplexCSP.Structure.DegreeStructuralCollapse

/-! # The actual degree-restricted hard implication through Lin's gadget compiler

A literal failure of degree BO supplies a finite degree-divisible presentation
over the prescribed original field. Its singleton language is ordinary non-BO.
The same basis is used throughout the final unrestricted-to-degree substitution.
-/
noncomputable section
open Classical
namespace ComplexCSP.ComplexityDegreeHardnessCore
open PlanarHom PlanarHom.Complexity AlgebraicProductInterpolation
variable {D K : Type} [Fintype D] [Field K] [Algebra ℚ K] {s d : ℕ}

/-- Every witness and exact-field reweighting is extracted internally. The
internal theorem is valid for arbitrary δ, including the vacuous δ=0 case. -/
theorem hard_of_not_degreeJointBO_of_potts (basis : Module.Basis (Fin d) ℚ K)
    (σ : K →+* ℂ) (M : Language D K (Fin s)) (δ : ℕ)
    (hPotts : RealLanguage.PositivePottsFoundation) (hnot : ¬DegreeJointBO (M.mapValues σ) δ) :
    PromisedSharpPHard (ComplexityGadgetSubstitution.degreePartitionProblem M basis δ) := by
  obtain ⟨n,hn,P,hP,hbad⟩ := DegreeObstructionWitness.exists_singleton M σ δ hnot
  have hh := ComplexityNonBOHardnessCore.hard_of_not_jointBO_of_potts basis σ
    (GramGadget.language P.table) hPotts hbad
  exact hh.trans (ComplexityGadgetSubstitution.reduction basis (fun _ => P)
    (fun _ _ => rfl) δ (fun _ => hP))

end ComplexCSP.ComplexityDegreeHardnessCore
