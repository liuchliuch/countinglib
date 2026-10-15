import Paper2.Paper1ProvedOddUnaryNRCanonicalSource
import Paper2.Paper1ProvedOddUnaryNRCanonicalJordan
import Paper2.Paper1ProvedOddUnaryNRSmallCoefficients

/-! A unary outside the canonical sheared class produces a real nonsingular
Jordan transfer by capping the actual W graph. The physical edge remains the
original equality edge; its Gram matrix is retained explicitly. -/
namespace Paper2.Paper1Proved.OddUnary.NRUnaryExit
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.FinitePGL2.Stabilization
open OrdinaryNegativeCubicGadgets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

theorem action_unary (R : InvertibleKernel) (f : Holant.Signature AlgebraicComplex 1)
    (b : Bool) : R.action f (fun _ => b)=
    R.matrix b false*f (fun _ => false)+R.matrix b true*f (fun _ => true) := by
  unfold InvertibleKernel.action Holant.Signature.coordinateAction
  rw [←(Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  simp only [Fin.prod_univ_one,Fintype.sum_bool]
  exact add_comm _ _

def cross (R : InvertibleKernel) : AlgebraicComplex :=
  R.matrix false false*R.matrix false true+R.matrix true false*R.matrix true true

def rightNorm (R : InvertibleKernel) : AlgebraicComplex :=
  R.matrix false true^2+R.matrix true true^2

variable {K : Type} [Field K] {r : ℕ} {a : ℕ → ℕ}
variable {H : (i : Fin r) → Holant.Signature K (a i.val)}
variable {phi : K →+* AlgebraicComplex} {R0 : InvertibleKernel} {v : Bool → AlgebraicComplex}
variable (S : NRCanonical.Receipt (H:=H) phi R0 v)

theorem zero_cap_value (b : Bool) :
    RingHomRealization.mapSignature phi (S.caps false).network.denote (fun _ => b)=
      S.zeroCoefficient*(2*S.basis.matrix b false+S.basis.matrix b true) := by
  rw [S.zeroForm,action_unary]
  simp [NR.row,Holant.weight]
  ring

theorem gram_right : rightNorm S.basis=-2*cross S.basis := by
  have dual := S.dual false true
  simp only [NR.columnPair,Fintype.sum_bool,Bool.true_eq_false,ite_false] at dual
  rw [zero_cap_value S true,zero_cap_value S false] at dual
  have fact : S.zeroCoefficient*(rightNorm S.basis+2*cross S.basis)=0 := by
    unfold rightNorm cross
    linear_combination dual
  have h := (mul_eq_zero.mp fact).resolve_left S.zeroCoefficientNonzero
  linear_combination h

theorem cross_nonzero : cross S.basis≠0 := by
  intro zero
  have dual := S.dual false false
  simp only [NR.columnPair,Fintype.sum_bool,ite_true] at dual
  rw [zero_cap_value S true,zero_cap_value S false] at dual
  have h : S.capScalars false=0 := by
    unfold cross at zero
    linear_combination -dual+2*S.zeroCoefficient*S.isotropic+S.zeroCoefficient*zero
  exact S.capNonzero false h

theorem columnPair_action (f : Holant.Signature AlgebraicComplex 1) :
    NR.columnPair (S.basis.action f) S.basis.matrix false=
      cross S.basis*f (fun _ => true) ∧
    NR.columnPair (S.basis.action f) S.basis.matrix true=
      cross S.basis*(f (fun _ => false)-2*f (fun _ => true)) := by
  simp only [NR.columnPair,Fintype.sum_bool,action_unary]
  constructor
  · unfold cross
    linear_combination f (fun _ => false)*S.isotropic
  · have right := gram_right S
    unfold rightNorm cross at right
    unfold cross
    linear_combination f (fun _ => true)*right

def binary (U : NoXOrdinaryGraphAdjoin.Output H 1) :
    NoXOrdinaryGraphAdjoin.Output H 2 := NR.ActualCaps.output U S.ternary 0

def binaryKernel (c a b : AlgebraicComplex) : Holant.Kernel AlgebraicComplex :=
  fun i j => c*(if i then (if j then 0 else b) else (if j then b else a))

def jordanKernel (a b : AlgebraicComplex) : Holant.Kernel AlgebraicComplex :=
  fun i j => if i then (if j then b else 0) else (if j then a else b)

theorem cap_row (f : Holant.Signature AlgebraicComplex 1)
    (x : Fin 2 → Bool) :
    (∑ b : Bool,NR.columnPair (S.basis.action f) S.basis.matrix b*
      NR.row (n:=3) S.ternaryCoefficient (Fin.cons b x))=
    kernelSignature (binaryKernel (S.ternaryCoefficient*cross S.basis)
      (f (fun _ => false)) (f (fun _ => true))) x := by
  have pairings := columnPair_action S f
  simp only [Fintype.sum_bool,pairings.1,pairings.2,NR.row,Holant.weight,
    Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,kernelSignature,binaryKernel]
  have xx : x=![x 0,x 1] := by funext i;fin_cases i <;> rfl
  rw [xx]
  cases x 0 <;> cases x 1 <;> simp <;> ring

theorem binary_form (U : NoXOrdinaryGraphAdjoin.Output H 1) :
    S.basis.symm.action (RingHomRealization.mapSignature phi (binary S U).network.denote)=
      kernelSignature (binaryKernel (S.ternaryCoefficient*cross S.basis)
        ((S.basis.symm.action (RingHomRealization.mapSignature phi U.network.denote)) (fun _ => false))
        ((S.basis.symm.action (RingHomRealization.mapSignature phi U.network.denote)) (fun _ => true))) := by
  let f := S.basis.symm.action (RingHomRealization.mapSignature phi U.network.denote)
  have uf : RingHomRealization.mapSignature phi U.network.denote=S.basis.action f :=
    (S.basis.action_symm_action _).symm
  change S.basis.symm.action
    (RingHomRealization.mapSignature phi (NR.ActualCaps.output U S.ternary 0).network.denote)=_
  rw [NR.ActualCaps.mapped_denote,S.ternaryForm,uf]
  have h := NR.cap_action S.basis.matrix (S.basis.action f)
    (NR.row (n:=3) S.ternaryCoefficient) (0 : Fin 3)
  change NR.cap (S.basis.action f) (S.basis.action (NR.row S.ternaryCoefficient)) 0=
    S.basis.action _ at h
  rw [h,InvertibleKernel.symm_action_action]
  funext x
  simpa [Fin.insertNth_zero,InvertibleKernel.symm_action_action] using cap_row S f x

theorem gram_entries :
    Holant.Kernel.pullback Holant.Signature.equality S.basis.matrix=
      fun i j => cross S.basis*(if i then (if j then -2 else 1) else (if j then 1 else 0)) := by
  funext i j
  cases i <;> cases j <;>
    simp [Holant.Kernel.pullback,Holant.Kernel.mul_apply,Holant.Kernel.transpose,
      cross,mul_comm]
  · linear_combination S.isotropic
  · have h := gram_right S
    unfold rightNorm cross at h
    linear_combination h

theorem binary_transfer (U : NoXOrdinaryGraphAdjoin.Output H 1) :
    Holant.Kernel.mul
      (binaryMatrix (S.basis.symm.action
        (RingHomRealization.mapSignature phi (binary S U).network.denote)))
      (Holant.Kernel.pullback Holant.Signature.equality S.basis.matrix)=
      fun i j => (S.ternaryCoefficient*cross S.basis^2)*jordanKernel
        (((S.basis.symm.action (RingHomRealization.mapSignature phi U.network.denote)) (fun _ => false))-
          2*((S.basis.symm.action (RingHomRealization.mapSignature phi U.network.denote)) (fun _ => true)))
        ((S.basis.symm.action (RingHomRealization.mapSignature phi U.network.denote)) (fun _ => true)) i j := by
  rw [binary_form,gram_entries]
  funext i j
  cases i <;> cases j <;>
    simp [binaryMatrix,kernelSignature,binaryKernel,jordanKernel,Holant.Kernel.mul_apply] <;> ring

theorem outside_parameters (U : NoXOrdinaryGraphAdjoin.Output H 1)
    (outside : ¬NR.Closed
      (S.basis.symm.action (RingHomRealization.mapSignature phi U.network.denote))) :
    ((S.basis.symm.action (RingHomRealization.mapSignature phi U.network.denote)) (fun _ => true))≠0 ∧
    (((S.basis.symm.action (RingHomRealization.mapSignature phi U.network.denote)) (fun _ => false))-
      2*((S.basis.symm.action (RingHomRealization.mapSignature phi U.network.denote)) (fun _ => true)))≠0 := by
  obtain ⟨b,a⟩ := NR.outside_unary _ outside
  exact ⟨b,sub_ne_zero.mpr a⟩

theorem gram_cross_decomposition (i j : Bool) :
    S.basis.matrix i false*S.basis.matrix j true+
      S.basis.matrix i true*S.basis.matrix j false=
    cross S.basis*(if i=j then 1 else 0)-
      2*S.basis.matrix i false*S.basis.matrix j false := by
  apply mul_left_cancel₀ (cross_nonzero S)
  have right := gram_right S
  have rightzero : rightNorm S.basis+2*cross S.basis=0 := by
    linear_combination right
  unfold rightNorm cross at rightzero
  unfold cross
  cases i <;> cases j <;>
    simp only [Bool.false_eq_true,Bool.true_eq_false,ite_true,ite_false,mul_one,mul_zero]
  · linear_combination S.basis.matrix false false^2*rightzero-
      S.basis.matrix true true^2*S.isotropic
  · linear_combination S.basis.matrix false false*S.basis.matrix true false*rightzero+
      S.basis.matrix false true*S.basis.matrix true true*S.isotropic
  · linear_combination S.basis.matrix false false*S.basis.matrix true false*rightzero+
      S.basis.matrix false true*S.basis.matrix true true*S.isotropic
  · linear_combination S.basis.matrix true false^2*rightzero-
      S.basis.matrix false true^2*S.isotropic

theorem physical_binary_expansion (U : NoXOrdinaryGraphAdjoin.Output H 1) :
    RingHomRealization.mapSignature phi (binary S U).network.denote=
      kernelSignature (fun i j => (S.ternaryCoefficient*cross S.basis)*
        (((S.basis.symm.action (RingHomRealization.mapSignature phi U.network.denote)) (fun _ => false))*
          S.basis.matrix i false*S.basis.matrix j false+
        ((S.basis.symm.action (RingHomRealization.mapSignature phi U.network.denote)) (fun _ => true))*
          (S.basis.matrix i false*S.basis.matrix j true+
            S.basis.matrix i true*S.basis.matrix j false))) := by
  calc
    _ = S.basis.action (kernelSignature (binaryKernel (S.ternaryCoefficient*cross S.basis)
        ((S.basis.symm.action (RingHomRealization.mapSignature phi U.network.denote)) (fun _ => false))
        ((S.basis.symm.action (RingHomRealization.mapSignature phi U.network.denote)) (fun _ => true)))) := by
      rw [←binary_form,InvertibleKernel.action_symm_action]
    _ = _ := by
      rw [InvertibleKernel.action,coordinateAction_kernelSignature]
      funext x
      simp [kernelSignature,Holant.Kernel.mul_apply,Holant.Kernel.transpose,binaryKernel]
      ring

/-- The actual binary produced from an outside unary has a nonzero repeated
eigenvalue and a nonzero nilpotent part, in the original ordinary basis. -/
theorem jordan_receipt (U : NoXOrdinaryGraphAdjoin.Output H 1)
    (outside : ¬NR.Closed
      (S.basis.symm.action (RingHomRealization.mapSignature phi U.network.denote))) :
    Nonempty (NRCanonical.JordanReceipt (H:=H) phi) := by
  let f := S.basis.symm.action (RingHomRealization.mapSignature phi U.network.denote)
  let u : Bool → AlgebraicComplex := fun t => S.basis.matrix t false
  let lambda := S.ternaryCoefficient*cross S.basis^2*f (fun _ => true)
  let gamma := S.ternaryCoefficient*cross S.basis*(f (fun _ => false)-2*f (fun _ => true))
  obtain ⟨hb,ha⟩ := outside_parameters S U outside
  have hl : lambda≠0 := mul_ne_zero
    (mul_ne_zero S.ternaryCoefficientNonzero (pow_ne_zero _ (cross_nonzero S))) hb
  have hg : gamma≠0 := mul_ne_zero
    (mul_ne_zero S.ternaryCoefficientNonzero (cross_nonzero S)) ha
  have form : RingHomRealization.mapSignature phi (binary S U).network.denote=
      kernelSignature (NRCanonical.jordanMatrix lambda gamma u) := by
    rw [physical_binary_expansion]
    funext x
    change (S.ternaryCoefficient*cross S.basis)*
      (f (fun _ => false)*S.basis.matrix (x 0) false*S.basis.matrix (x 1) false+
        f (fun _ => true)*(S.basis.matrix (x 0) false*S.basis.matrix (x 1) true+
          S.basis.matrix (x 0) true*S.basis.matrix (x 1) false))=_
    rw [gram_cross_decomposition S (x 0) (x 1)]
    dsimp [kernelSignature,NRCanonical.jordanMatrix,lambda,gamma,u]
    split_ifs <;> ring
  exact ⟨{
    graph := binary S U
    repeated := u
    repeatedFalseNonzero := NRCanonical.isotropic_first_nonzero S.basis S.isotropic
    isotropic := S.isotropic
    eigenvalue := lambda
    defect := gamma
    eigenvalueNonzero := hl
    defectNonzero := hg
    form := form
    determinantNonzero := by
      rw [NRCanonical.jordan_determinant lambda gamma u S.isotropic]
      exact pow_ne_zero _ hl }⟩

end
end Paper2.Paper1Proved.OddUnary.NRUnaryExit

