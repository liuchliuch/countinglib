import Paper2.FixedFieldOutput.ResidualBranches
import Paper2.FixedFieldOutput.Reductions

/-! Complete original-graph Bell reductions with canonical fixed-field answers.
The only mathematical inputs are a literal nonzero scalar RM core and, for I,
the high-charge support condition. Every preprocessing, oracle and arithmetic
stage is a concrete finite-machine construction. -/
namespace Paper2.FixedFieldOutput.BellReductions
open Computability Paper2.Complexity Paper2.ExactInput Paper2.Problem
open Paper2.Tractable Paper2.RelativeEO Paper2.BellReduction
noncomputable section

/-- The core label is selected once from the fixed language, not discovered by
semantic table equality while processing an input graph. -/
 def reduction (L : Language) (c : AlgebraicComplex) (hc : c ≠ 0)
    (hcore : (⟨8,fun x => c * ReedMuller.core x⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (d l : Bool)
    (B : ∀ i : Fin 3, ResidualCompiler.Branch L (bellTable d l) i) :
    LengthControlledOracleReduction
      (inputEncoding (tagged L (bellTable d l))) (answerEncoding (tagged L (bellTable d l)))
      (inputEncoding L) (answerEncoding L)
      (answer .nativeX (tagged L (bellTable d l))) (answer .nativeX L) := by
  let i : Fin L.count := Classical.choose hcore
  have hi := Classical.choose_spec hcore
  have ha : L.arity i.val = 8 := congrArg Sigma.fst hi
  let T := tagged L (bellTable d l)
  have hit : i.val + 1 < T.count := by dsimp [T]; exact Nat.add_lt_add_right i.isLt 1
  have hct : (⟨T.arity (i.val+1),T.signature ⟨i.val+1,hit⟩⟩ : AnySignature AlgebraicComplex) =
      ⟨8,fun x => c * ReedMuller.core x⟩ := (tagged_succ L (bellTable d l) i).trans hi
  let norm := normalizationReduction T (tagged_arity_zero L (bellTable d l))
    (i.val+1) hit (by simpa [T] using ha) c hc d l (by simp [T])
    (tagged_zero L (bellTable d l)) hct
  exact norm.controlledCompose (ResidualCompiler.reduction L (bellTable d l) B)

 theorem Y (L : Language) (c : AlgebraicComplex) (hc : c ≠ 0)
    (hcore : (⟨8,fun x => c * ReedMuller.core x⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Reduces .nativeX (tagged L (bellTable true true)) L :=
  ⟨reduction L c hc hcore true true (ResidualBranches.branchesY L)⟩

 theorem I (L : Language) (hHigh : HighCharge L.family)
    (c : AlgebraicComplex) (hc : c ≠ 0)
    (hcore : (⟨8,fun x => c * ReedMuller.core x⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Reduces .nativeX (tagged L (bellTable false false)) L :=
  ⟨reduction L c hc hcore false false (ResidualBranches.branchesI L hHigh)⟩

end
end Paper2.FixedFieldOutput.BellReductions
