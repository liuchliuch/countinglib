import ComplexCSP.Complexity.PinnedEvaluator
import ComplexCSP.Complexity.PinnedOuterCorrectnessDegree
import ComplexCSP.Complexity.CSPPromisedFP
import ComplexCSP.Complexity.CSPDomainTransport
import ComplexCSP.Algebra.GlobalConditionsColorTransport
import ComplexCSP.Complexity.EmptyDomain

/-! # Closed positive fixed-language complexity implications

The genuine finite-control FP program is composed from the actual initial
support, pinned class/layer, bounded outer iteration and final product machines.
All semantic and size hypotheses are derived from the literal global BO
condition. Arbitrary finite colors and prescribed rational-basis coefficient
fields retain their original instance/output encoding. No algorithm or FP
premise is assumed, and no exclusivity with #P-hardness is asserted.
-/
noncomputable section
namespace ComplexCSP.ComplexityPositiveFP
open PlanarHom PlanarHom.Complexity ComplexityCSPCode
open ComplexityCSPPromisedFP ComplexityPinnedEvaluator ComplexityCSPColorRelabeling
variable {D K : Type} [Fintype D] [Field K] [DecidableEq K] [Algebra ℚ K]
variable {s dimension : ℕ}

omit [Fintype D] [DecidableEq K] in
/-- Algebraicity follows from the supplied finite rational basis. -/
theorem realization_algebraic (basis : Module.Basis (Fin dimension) ℚ K)
    (σ : K →+* ℂ) (L : Language D K (Fin s)) :
    ∀ i a, IsAlgebraic ℚ ((L.mapValues σ).value i a) := by
  letI : FiniteDimensional ℚ K := Module.Finite.of_basis basis
  intro i a
  exact (IsIntegral.map σ.toRatAlgHom (IsIntegral.of_finite (R:=ℚ) (L.value i a))).isAlgebraic

/-- Closed ordinary evaluator on finite ordinal colors, including the empty
boundary. The FP assertion is exactly the valid canonical-code promise. -/
theorem fin_jointBO_inFP {d : ℕ} (L : Language (Fin d) K (Fin s))
    (basis : Module.Basis (Fin dimension) ℚ K) (σ : K →+* ℂ)
    (hBO : JointBO (L.mapValues σ)) : (ComplexityCSPCountReduction.partitionProblem L basis).InFP := by
  by_cases hd : d=0
  · subst d
    exact partition_inFP L basis (partition L) (ComplexityEmptyDomain.fp_partition L basis) (fun _ _ => rfl)
  · letI : NeZero d := ⟨hd⟩
    let a : Fin d := ⟨0,Nat.pos_of_ne_zero hd⟩
    obtain ⟨m,space,_,hcorrect⟩ := ComplexityPinnedOuter.jointBO_actual_evaluator L basis σ
      (realization_algebraic basis σ L) hBO a
    apply partition_inFP L basis (run L basis m a (ComplexityLabelExtension.restrictedSpace L basis) space)
      (fp_run L basis m a (ComplexityLabelExtension.restrictedSpace L basis) space)
    intro g hg
    unfold run
    rw [startContext_eq L m a g hg]
    exact hcorrect g hg

/-- Direct degree-family positive implication. Ordinary JointBO is not needed,
and only genuine δ-divisible instances are in the source promise. -/
theorem fin_degreeJointBO_inFP {d : ℕ} (L : Language (Fin d) K (Fin s))
    (basis : Module.Basis (Fin dimension) ℚ K) (σ : K →+* ℂ) {δ : ℕ} (hδ : 0<δ)
    (hBO : DegreeJointBO (L.mapValues σ) δ) :
    (ComplexityGadgetSubstitution.degreePartitionProblem L basis δ).InFP := by
  by_cases hd : d=0
  · subst d
    exact degreePartition_inFP L basis δ (partition L) (ComplexityEmptyDomain.fp_partition L basis)
      (fun _ _ => rfl)
  · letI : NeZero d := ⟨hd⟩
    let a : Fin d := ⟨0,Nat.pos_of_ne_zero hd⟩
    obtain ⟨m,space,_,hcorrect⟩ := ComplexityPinnedOuter.degreeJointBO_actual_evaluator L basis σ hδ
      (realization_algebraic basis σ L) hBO a
    apply degreePartition_inFP L basis δ (run L basis m a (ComplexityLabelExtension.restrictedSpace L basis) space)
      (fp_run L basis m a (ComplexityLabelExtension.restrictedSpace L basis) space)
    rintro g ⟨hg,hdegree⟩
    unfold run
    rw [startContext_eq L m a g hg]
    exact hcorrect g hg hdegree

/-- Arbitrary finite domain, in its original exact field-output presentation. -/
theorem jointBO_inFP (L : Language D K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
    (σ : K →+* ℂ) (hBO : JointBO (L.mapValues σ)) :
    (ComplexityCSPCountReduction.partitionProblem L basis).InFP := by
  classical
  let e := (Fintype.equivFin D).symm
  apply ComplexityCSPDomainTransport.inFP_of_fin L basis
  apply fin_jointBO_inFP (reindex L e) basis σ
  rw [GlobalConditionsColorTransport.reindex_mapValues]
  exact (GlobalConditionsColorTransport.jointBO_reindex_iff e (L.mapValues σ)).mpr hBO

/-- Arbitrary finite domain and a positive occurrence-degree modulus. -/
theorem degreeJointBO_inFP (L : Language D K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
    (σ : K →+* ℂ) {δ : ℕ} (hδ : 0<δ) (hBO : DegreeJointBO (L.mapValues σ) δ) :
    (ComplexityGadgetSubstitution.degreePartitionProblem L basis δ).InFP := by
  classical
  let e := (Fintype.equivFin D).symm
  apply ComplexityCSPDomainTransport.degree_inFP_of_fin L basis δ
  apply fin_degreeJointBO_inFP (reindex L e) basis σ hδ
  rw [GlobalConditionsColorTransport.reindex_mapValues]
  exact (GlobalConditionsColorTransport.degreeJointBO_reindex_iff e (L.mapValues σ) δ).mpr hBO

/-- Original Cai–Chen positive branch; the fixed basis supplies algebraicity. -/
theorem conditions_inFP [Nonempty D] (L : Language D K (Fin s))
    (basis : Module.Basis (Fin dimension) ℚ K) (σ : K →+* ℂ)
    (h : CaiChenConditions (L.mapValues σ)) :
    (ComplexityCSPCountReduction.partitionProblem L basis).InFP :=
  jointBO_inFP L basis σ ((structural_collapse (L.mapValues σ) (realization_algebraic basis σ L)).mp h)

/-- Original Lin positive branch for the literal degree-generated conditions. -/
theorem degreeConditions_inFP [Nonempty D] (L : Language D K (Fin s))
    (basis : Module.Basis (Fin dimension) ℚ K) (σ : K →+* ℂ) {δ : ℕ} (hδ : 0<δ)
    (h : DegreeCaiChenConditions (L.mapValues σ) δ) :
    (ComplexityGadgetSubstitution.degreePartitionProblem L basis δ).InFP :=
  degreeJointBO_inFP L basis σ hδ
    ((degree_structural_collapse (L.mapValues σ) δ (realization_algebraic basis σ L)).mp h)

end ComplexCSP.ComplexityPositiveFP
