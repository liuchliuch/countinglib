import Paper2.Paper1ProvedOddUnaryNRCanonicalAlgebra

/-! Exact NR generator forms in the concrete exceptional chart. -/
namespace Paper2.Paper1Proved.OddUnary.NRCanonical
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384

theorem coordinate_row_three (A : Kernel AlgebraicComplex) (d : AlgebraicComplex) :
    Holant.Signature.coordinateAction (fun _ => A) (NR.row (n:=3) d) =
      fun x => d*GlobalCloseCompletionIndependentPinsWCore.image A x+
        2*d*A (x 0) false*A (x 1) false*A (x 2) false := by
  rw [GlobalCloseCompletionIndependentPinsWCore.coordinate]
  funext x
  simp only [GlobalCloseCompletionTernaryGHZCore.action,Matrix.of_apply]
  simp only [NR.row,Holant.weight,Fin.sum_univ_three]
  simp [GlobalCloseCompletionIndependentPinsWCore.image]
  ring

theorem coordinate_row_one (A : Kernel AlgebraicComplex) (d : AlgebraicComplex) :
    Holant.Signature.coordinateAction (fun _ => A) (NR.row (n:=1) d) =
      fun x => 2*d*A (x 0) false+d*A (x 0) true := by
  let E : Bool ≃ (Fin 1 → Bool) := {
    toFun := fun v _ => v
    invFun := fun x => x 0
    left_inv := fun _ => rfl
    right_inv := by intro x;funext i;rw [Fin.eq_zero i] }
  funext x
  unfold Holant.Signature.coordinateAction
  rw [←E.sum_comp]
  simp [E,NR.row,Holant.weight]
  ring

theorem coordinate_pin_one (A : Kernel AlgebraicComplex) (d : AlgebraicComplex) :
    Holant.Signature.coordinateAction (fun _ => A) (NR.pin (n:=1) d) =
      fun x => d*A (x 0) false := by
  let E : Bool ≃ (Fin 1 → Bool) := {
    toFun := fun v _ => v
    invFun := fun x => x 0
    left_inv := fun _ => rfl
    right_inv := by intro x;funext i;rw [Fin.eq_zero i] }
  funext x
  unfold Holant.Signature.coordinateAction
  rw [←E.sum_comp]
  simp [E,NR.pin,Holant.weight]
  ring

theorem w_generator (R : InvertibleKernel) (v : Bool → AlgebraicComplex)
    (ha : alpha R.matrix v≠0) (hb : beta R.matrix v≠0) :
    GlobalCloseCompletionIndependentPinsWCore.image R.matrix =
      (chart R v ha hb).action (NR.row (1/(18*alpha R.matrix v*beta R.matrix v^2))) := by
  change _ = Holant.Signature.coordinateAction (fun _ => chartKernel R.matrix v) _
  rw [coordinate_row_three]
  funext x
  simp only [GlobalCloseCompletionIndependentPinsWCore.image,chartKernel,Bool.false_eq_true,ite_false,ite_true]
  field_simp [ha,hb]
  ring

theorem zero_pin_generator (R : InvertibleKernel) (v : Bool → AlgebraicComplex)
    (iso : R.matrix false false^2+R.matrix true false^2=0)
    (he : exceptional R.matrix v) (ha : alpha R.matrix v≠0) (hb : beta R.matrix v≠0) :
    (fun x : Fin 1 → Bool => v (x 0)) =
      (chart R v ha hb).action (NR.row (1/(2*TernaryW.cross R.matrix))) := by
  change _ = Holant.Signature.coordinateAction (fun _ => chartKernel R.matrix v) _
  rw [coordinate_row_one]
  have hp := TernaryW.isotropic_cross_nonzero R iso
  funext x
  simp only [chartKernel,Bool.false_eq_true,ite_false,ite_true]
  apply (mul_left_cancel₀ hp)
  field_simp [hp]
  have h := pin_expansion R v iso he (x 0)
  linear_combination h

theorem isotropic_pin_generator (R : InvertibleKernel) (v : Bool → AlgebraicComplex)
    (ha : alpha R.matrix v≠0) (hb : beta R.matrix v≠0) (kappa : AlgebraicComplex) :
    (fun x : Fin 1 → Bool => kappa*R.matrix (x 0) false) =
      (chart R v ha hb).action (NR.pin (kappa/(3*beta R.matrix v))) := by
  change _ = Holant.Signature.coordinateAction (fun _ => chartKernel R.matrix v) _
  rw [coordinate_pin_one]
  funext x
  simp only [chartKernel,Bool.false_eq_true,ite_false]
  field_simp [hb]

end
end Paper2.Paper1Proved.OddUnary.NRCanonical

