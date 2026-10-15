import Paper2.Paper1ProvedOddUnaryNRCanonicalPacket

/-! The other concrete W exit supplies an actual nonscalar Jordan binary.
This is a graph receipt for interpolation, with no hardness conclusion. -/
namespace Paper2.Paper1Proved.OddUnary.NRCanonical
open Paper2.ExactInput
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384

def jordanMatrix (eigenvalue defect : AlgebraicComplex) (u : Bool → AlgebraicComplex) :
    Kernel AlgebraicComplex := fun i j => (if i=j then eigenvalue else 0)+defect*u i*u j

theorem jordan_determinant (eigenvalue defect : AlgebraicComplex) (u : Bool → AlgebraicComplex)
    (iso : u false^2+u true^2=0) :
    SymmetricBinaryPullback.determinant (jordanMatrix eigenvalue defect u)=eigenvalue^2 := by
  simp only [SymmetricBinaryPullback.determinant,jordanMatrix,Bool.false_eq_true,ite_true,ite_false,
    Bool.true_eq_false]
  linear_combination eigenvalue*defect*iso

theorem isotropic_first_nonzero (R : InvertibleKernel)
    (iso : R.matrix false false^2+R.matrix true false^2=0) : R.matrix false false≠0 := by
  intro zero
  have second : R.matrix true false=0 := by
    have square : R.matrix true false^2=0 := by simpa only [zero,zero_pow (by decide : 2≠0),zero_add] using iso
    exact sq_eq_zero_iff.mp square
  apply SymmetricBinaryPullback.determinant_ne_zero R
  simp [SymmetricBinaryPullback.determinant,zero,second]

theorem cap_jordan_matrix (R : InvertibleKernel) (v : Bool → AlgebraicComplex)
    (iso : R.matrix false false^2+R.matrix true false^2=0) :
    TernaryW.cap_right R.matrix R.matrix R.matrix v=
      jordanMatrix (alpha R.matrix v*TernaryW.cross R.matrix)
        ((beta R.matrix v*TernaryW.cross R.matrix+alpha R.matrix v*excitationNorm R.matrix)/
          TernaryW.cross R.matrix) (fun t => R.matrix t false) := by
  have hp := TernaryW.isotropic_cross_nonzero R iso
  funext i j
  apply mul_left_cancel₀ hp
  have polynomial : TernaryW.cross R.matrix*TernaryW.cap_right R.matrix R.matrix R.matrix v i j=
      TernaryW.cross R.matrix*(if i=j then alpha R.matrix v*TernaryW.cross R.matrix else 0)+
        (beta R.matrix v*TernaryW.cross R.matrix+alpha R.matrix v*excitationNorm R.matrix)*
          R.matrix i false*R.matrix j false := by
    cases i <;> cases j <;>
      simp only [Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false,TernaryW.cap_right,
        TernaryW.cross,alpha,beta,excitationNorm]
    · linear_combination -(R.matrix false false*v false+R.matrix true false*v true)*R.matrix true true^2*iso
    · linear_combination (R.matrix false false*v false+R.matrix true false*v true)*R.matrix false true*R.matrix true true*iso
    · linear_combination (R.matrix false false*v false+R.matrix true false*v true)*R.matrix false true*R.matrix true true*iso
    · linear_combination -(R.matrix false false*v false+R.matrix true false*v true)*R.matrix false true^2*iso
  rw [polynomial]
  simp only [jordanMatrix,mul_add]
  field_simp [hp]

section Graph
variable {K : Type} [Field K] {r : ℕ} {b : ℕ → ℕ}
variable {H : (i : Fin r) → Holant.Signature K (b i.val)}

structure JordanReceipt (phi : K →+* AlgebraicComplex) : Type where
  graph : NoXOrdinaryGraphAdjoin.Output H 2
  repeated : Bool → AlgebraicComplex
  repeatedFalseNonzero : repeated false≠0
  isotropic : repeated false^2+repeated true^2=0
  eigenvalue : AlgebraicComplex
  defect : AlgebraicComplex
  eigenvalueNonzero : eigenvalue≠0
  defectNonzero : defect≠0
  form : RingHomRealization.mapSignature phi graph.network.denote=
    kernelSignature (jordanMatrix eigenvalue defect repeated)
  determinantNonzero : SymmetricBinaryPullback.determinant (jordanMatrix eigenvalue defect repeated)≠0

theorem scaled_cap_mapped (phi : K →+* AlgebraicComplex) (N : Macro H 3) (P : Macro H 1)
    (R : InvertibleKernel) (v : Bool → AlgebraicComplex) (delta : AlgebraicComplex)
    (form : RingHomRealization.mapSignature phi N.network.denote=
      fun x => delta*GlobalCloseCompletionIndependentPinsWCore.image R.matrix x)
    (pin : RingHomRealization.mapSignature phi P.network.denote=fun x => v (x 0)) :
    RingHomRealization.mapSignature phi (GlobalCloseCompletionSymmetricGHZCapGraph.cap N P).network.denote=
      kernelSignature (fun i j => delta*TernaryW.cap_right R.matrix R.matrix R.matrix v i j) := by
  funext x
  rw [RingHomRealization.mapSignature,GlobalCloseCompletionSymmetricGHZCapGraph.cap_value,map_add,map_mul,map_mul]
  have nf (t : Bool) : phi (N.network.denote ![t,x 0,x 1])=
      delta*GlobalCloseCompletionIndependentPinsWCore.image R.matrix ![t,x 0,x 1] := congrFun form _
  have pf (t : Bool) : phi (P.network.denote (fun _ => t))=v t := congrFun pin _
  simp [nf,pf,GlobalCloseCompletionIndependentPinsWCore.image,kernelSignature,TernaryW.cap_right]
  ring

end Graph

theorem Prepared.jordan_receipt {L : Language} {S : IsotropicWSource L} (I : Prepared S)
    (he : ¬exceptional I.frame.matrix I.vector) :
    Nonempty (JordanReceipt (H:=S.source.H) S.source.K.subtype) := by
  let R := I.frame
  let v := I.vector
  let p := TernaryW.cross R.matrix
  let u : Bool → AlgebraicComplex := fun t => R.matrix t false
  let lambda := I.delta*alpha R.matrix v*p
  let gamma := I.delta*((beta R.matrix v*p+alpha R.matrix v*excitationNorm R.matrix)/p)
  have hp : p≠0 := TernaryW.isotropic_cross_nonzero R I.isotropic
  have hl : lambda≠0 := mul_ne_zero (mul_ne_zero I.deltaNonzero I.alphaNonzero) hp
  have hg : gamma≠0 := mul_ne_zero I.deltaNonzero (div_ne_zero he hp)
  let B := GlobalCloseCompletionSymmetricGHZCapGraph.cap I.ternary I.pin
  have form : RingHomRealization.mapSignature S.source.K.subtype B.network.denote=
      kernelSignature (jordanMatrix lambda gamma u) := by
    rw [scaled_cap_mapped S.source.K.subtype I.ternary I.pin R v I.delta I.ternaryForm I.pinForm,
      cap_jordan_matrix R v I.isotropic]
    funext x
    change I.delta*jordanMatrix (alpha R.matrix v*p)
      ((beta R.matrix v*p+alpha R.matrix v*excitationNorm R.matrix)/p) u (x 0) (x 1)=
        jordanMatrix lambda gamma u (x 0) (x 1)
    dsimp [jordanMatrix,lambda,gamma]
    split_ifs <;> ring
  exact ⟨{
    graph := output B
    repeated := u
    repeatedFalseNonzero := isotropic_first_nonzero R I.isotropic
    isotropic := I.isotropic
    eigenvalue := lambda
    defect := gamma
    eigenvalueNonzero := hl
    defectNonzero := hg
    form := form
    determinantNonzero := by rw [jordan_determinant lambda gamma u I.isotropic];exact pow_ne_zero _ hl }⟩

theorem concrete_exits {L : Language} (S : IsotropicWSource L) :
    Nonempty (JordanReceipt (H:=S.source.H) S.source.K.subtype) ∨
      ∃ R : InvertibleKernel,∃ v : Bool → AlgebraicComplex,
        Nonempty (Receipt (H:=S.source.H) S.source.K.subtype R v) := by
  obtain ⟨I,branch⟩ := canonical_or_jordan S
  rcases branch with jordan|canonical
  · exact Or.inl (I.jordan_receipt jordan)
  · exact Or.inr ⟨I.frame,I.vector,canonical⟩

end
end Paper2.Paper1Proved.OddUnary.NRCanonical

