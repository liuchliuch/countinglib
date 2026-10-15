import Paper2.Paper1ProvedOddUnaryNRCanonicalForms
import Paper2.Paper1ProvedOddUnaryNRActualCaps

/-! Two concrete actual caps for the exceptional symmetric W chart. The
second cap is the literal ordinary self-loop of the actual symmetric W
graph, so all occurrences use the same original finite table. -/
namespace Paper2.Paper1Proved.OddUnary.NRCanonical
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open OrdinaryNegativeCubicGadgets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384

section Graph
variable {K : Type} [Field K] {r : ℕ} {b : ℕ → ℕ}
variable {H : (i : Fin r) → Holant.Signature K (b i.val)}

theorem symmetric_trace (phi : K →+* AlgebraicComplex) (N : Macro H 3)
    (R : InvertibleKernel) (delta : AlgebraicComplex)
    (iso : R.matrix false false^2+R.matrix true false^2=0)
    (form : RingHomRealization.mapSignature phi N.network.denote=
      fun x => delta*GlobalCloseCompletionIndependentPinsWCore.image R.matrix x) :
    RingHomRealization.mapSignature phi N.contract.network.denote=
      fun x => (2*delta*TernaryW.cross R.matrix)*R.matrix (x 0) false := by
  funext x
  rw [RingHomRealization.mapSignature,Macro.contract_denote,map_add]
  have h0 := congrFun form (Fin.cons false (Fin.cons false x))
  have h1 := congrFun form (Fin.cons true (Fin.cons true x))
  change phi (N.network.denote (Fin.cons false (Fin.cons false x)))=_ at h0
  change phi (N.network.denote (Fin.cons true (Fin.cons true x)))=_ at h1
  rw [h0,h1]
  simp only [GlobalCloseCompletionIndependentPinsWCore.image,Fin.cons_zero,Fin.cons_one,TernaryW.cross]
  have tail (b : Bool) : (Fin.cons b (Fin.cons b x) : Fin 3 → Bool) (2 : Fin 3)=x 0 := by
    exact (Fin.cons_succ (α:=fun _ : Fin 3 => Bool) b
      (Fin.cons (α:=fun _ : Fin 2 => Bool) b x) (1 : Fin 2)).trans
      (Fin.cons_one (α:=fun _ : Fin 2 => Bool) b x)
  rw [tail,tail]
  linear_combination delta*R.matrix (x 0) true*iso

def output {n : ℕ} (N : Macro H n) : NoXOrdinaryGraphAdjoin.Output H n :=
  ⟨N.network,N.labels,N.exact,N.edges⟩

structure Receipt (phi : K →+* AlgebraicComplex)
    (R : InvertibleKernel) (v : Bool → AlgebraicComplex) : Type where
  basis : InvertibleKernel
  isotropic : basis.matrix false false^2+basis.matrix true false^2=0
  gramScale : AlgebraicComplex
  gramScaleNonzero : gramScale≠0
  gramForm : ∀ i j,basis.matrix false i*basis.matrix false j+basis.matrix true i*basis.matrix true j=
    if i=j then (if i then -2*gramScale else 0) else gramScale
  caps : Bool → NoXOrdinaryGraphAdjoin.Output H 1
  capScalars : Bool → AlgebraicComplex
  capNonzero : ∀ b,capScalars b≠0
  dual : ∀ b j,NR.columnPair (RingHomRealization.mapSignature phi (caps b).network.denote)
    basis.matrix j=if j=b then capScalars b else 0
  ternary : NoXOrdinaryGraphAdjoin.Output H 3
  ternaryCoefficient : AlgebraicComplex
  ternaryCoefficientNonzero : ternaryCoefficient≠0
  ternaryForm : RingHomRealization.mapSignature phi ternary.network.denote=
    basis.action (NR.row ternaryCoefficient)
  zeroCoefficient : AlgebraicComplex
  zeroCoefficientNonzero : zeroCoefficient≠0
  zeroForm : RingHomRealization.mapSignature phi (caps false).network.denote=
    basis.action (NR.row zeroCoefficient)
  lineCoefficient : AlgebraicComplex
  lineCoefficientNonzero : lineCoefficient≠0
  lineForm : RingHomRealization.mapSignature phi (caps true).network.denote=
    basis.action (NR.pin lineCoefficient)

theorem receipt (phi : K →+* AlgebraicComplex) (N : Macro H 3) (P : Macro H 1)
    (R : InvertibleKernel) (v : Bool → AlgebraicComplex) (delta : AlgebraicComplex)
    (hd : delta≠0) (iso : R.matrix false false^2+R.matrix true false^2=0)
    (norm : v false^2+v true^2≠0) (ha : alpha R.matrix v≠0)
    (he : exceptional R.matrix v)
    (form : RingHomRealization.mapSignature phi N.network.denote=
      fun x => delta*GlobalCloseCompletionIndependentPinsWCore.image R.matrix x)
    (pin : RingHomRealization.mapSignature phi P.network.denote=fun x => v (x 0)) :
    Nonempty (Receipt (H:=H) phi R v) := by
  have hb := exceptional_beta_nonzero R v iso norm ha he
  have hp := TernaryW.isotropic_cross_nonzero R iso
  let C := chart R v ha hb
  let kappa : AlgebraicComplex := 2*delta*TernaryW.cross R.matrix
  have hk : kappa≠0 := mul_ne_zero (mul_ne_zero (by norm_num) hd) hp
  let caps : Bool → NoXOrdinaryGraphAdjoin.Output H 1 :=
    fun b => if b then output N.contract else output P
  let a : Bool → AlgebraicComplex := fun b => if b then
    2*alpha R.matrix v*kappa*TernaryW.cross R.matrix else 3*alpha R.matrix v*beta R.matrix v
  have an : ∀ b,a b≠0 := by
    intro b
    cases b
    · exact mul_ne_zero (mul_ne_zero (by norm_num) ha) hb
    · exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha) hk) hp
  have dual : ∀ b j,NR.columnPair (RingHomRealization.mapSignature phi (caps b).network.denote)
      C.matrix j=if j=b then a b else 0 := by
    intro b j
    cases b
    · change NR.columnPair (RingHomRealization.mapSignature phi P.network.denote) (chartKernel R.matrix v) j=_
      rw [pin]
      simpa only [NR.columnPair,Fintype.sum_bool,a,Bool.false_eq_true,ite_false,add_comm] using
        chart_pin_pairing R.matrix v j
    · change NR.columnPair (RingHomRealization.mapSignature phi N.contract.network.denote) (chartKernel R.matrix v) j=_
      rw [symmetric_trace phi N R delta iso form]
      simpa only [NR.columnPair,Fintype.sum_bool,a,ite_true,add_comm,kappa] using
        chart_isotropic_pairing R.matrix v iso kappa j
  have ternaryForm : RingHomRealization.mapSignature phi N.network.denote=
      C.action (NR.row (delta/(18*alpha R.matrix v*beta R.matrix v^2))) := by
    rw [form,w_generator R v ha hb]
    have scaling := ClosureFactorTreeAction.coordinateAction_scale (fun _ : Fin 3 => C.matrix)
      (NR.row (1/(18*alpha R.matrix v*beta R.matrix v^2))) delta
    change (fun x => delta*Holant.Signature.coordinateAction (fun _ => C.matrix) _ x)=_
    rw [←scaling]
    congr 1
    funext x
    simp only [NR.row]
    split_ifs <;> ring
  exact ⟨{
    basis := C
    isotropic := chart_isotropic R.matrix v iso
    gramScale := 6*alpha R.matrix v*beta R.matrix v*TernaryW.cross R.matrix
    gramScaleNonzero := mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) ha) hb) hp
    gramForm := chart_gram R.matrix v iso he
    caps := caps
    capScalars := a
    capNonzero := an
    dual := dual
    ternary := output N
    ternaryCoefficient := delta/(18*alpha R.matrix v*beta R.matrix v^2)
    ternaryCoefficientNonzero := div_ne_zero hd
      (mul_ne_zero (mul_ne_zero (by norm_num) ha) (pow_ne_zero _ hb))
    ternaryForm := ternaryForm
    zeroCoefficient := 1/(2*TernaryW.cross R.matrix)
    zeroCoefficientNonzero := div_ne_zero one_ne_zero (mul_ne_zero (by norm_num) hp)
    zeroForm := pin.trans (zero_pin_generator R v iso he ha hb)
    lineCoefficient := kappa/(3*beta R.matrix v)
    lineCoefficientNonzero := div_ne_zero hk (mul_ne_zero (by norm_num) hb)
    lineForm := (symmetric_trace phi N R delta iso form).trans (isotropic_pin_generator R v ha hb kappa) }⟩

end Graph
end
end Paper2.Paper1Proved.OddUnary.NRCanonical

