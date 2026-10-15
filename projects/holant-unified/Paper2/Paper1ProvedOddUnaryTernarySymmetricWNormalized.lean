import Paper2.Paper1ProvedOddUnaryTernarySymmetricWGraph

/-! An actual isotropic W graph with an actual scalar zero pin produces a
nonzero scalar multiple of a symmetric W tensor in one invertible basis.
The basis records the output tensor; it is not adjoined as a graph vertex. -/
namespace Paper2.Paper1Proved.OddUnary.TernaryW
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open OrdinaryNegativeCubicGadgets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384

def shiftedKernel (A : Kernel AlgebraicComplex) (eta : AlgebraicComplex) : Kernel AlgebraicComplex :=
  fun v j => if j then A v true + eta * A v false else A v false

theorem shifted_determinant (A : Kernel AlgebraicComplex) (eta : AlgebraicComplex) :
    SymmetricBinaryPullback.determinant (shiftedKernel A eta) = SymmetricBinaryPullback.determinant A := by
  simp only [SymmetricBinaryPullback.determinant,shiftedKernel,Bool.false_eq_true,ite_false,ite_true]
  ring

def shiftedBasis (A : Holant.Tractable.InvertibleKernel) (eta : AlgebraicComplex) :
    Holant.Tractable.InvertibleKernel :=
  SymmetricBinaryPullback.invertibleOfDeterminant (shiftedKernel A.matrix eta)
    (by rw [shifted_determinant];exact SymmetricBinaryPullback.determinant_ne_zero A)

theorem aligned_normalized (A : Holant.Tractable.InvertibleKernel)
    (db dc eb ec : AlgebraicComplex) (hb : db ≠ 0) (hc : dc ≠ 0) :
    ∃ R : Holant.Tractable.InvertibleKernel,
      (∀ v, R.matrix v false = A.matrix v false) ∧
      aligned_value A.matrix db dc eb ec =
        (fun x => (db * dc) * GlobalCloseCompletionIndependentPinsWCore.image R.matrix x) := by
  let eta : AlgebraicComplex := (eb * dc + db * ec) / (3 * db * dc)
  let R := shiftedBasis A eta
  refine ⟨R,?_,?_⟩
  · intro v
    rfl
  · funext x
    change aligned_value A.matrix db dc eb ec x =
      db * dc * GlobalCloseCompletionIndependentPinsWCore.image (shiftedKernel A.matrix eta) x
    have coefficient : 3 * (db * dc * eta) = eb * dc + db * ec := by
      dsimp [eta]
      field_simp [hb,hc]
    simp only [aligned_value,GlobalCloseCompletionIndependentPinsWCore.image,shiftedKernel,Bool.false_eq_true,ite_true,ite_false]
    linear_combination -(A.matrix (x 0) false * A.matrix (x 1) false * A.matrix (x 2) false) * coefficient

section Graph
variable {K : Type} [Field K] {r : ℕ} {b : ℕ → ℕ}
variable {H : (i : Fin r) → Signature K (b i.val)}

theorem isotropic_symmetric_output (phi : K →+* AlgebraicComplex)
    (N : Macro H 3) (pin : Macro H 1) (c : AlgebraicComplex) (hc : c ≠ 0)
    (A B C : Holant.Tractable.InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote = W.image A.matrix B.matrix C.matrix)
    (zeroPin : RingHomRealization.mapSignature phi pin.network.denote =
      (fun x => if x 0 then 0 else c))
    (bc : W.gram (1 : AlgebraicComplex) B.matrix C.matrix false false = 0)
    (ab : W.gram 1 A.matrix B.matrix false false = 0)
    (ca : W.gram 1 C.matrix A.matrix false false = 0) :
    ∃ R : Holant.Tractable.InvertibleKernel, ∃ delta : AlgebraicComplex,
      delta ≠ 0 ∧
      (∀ v, R.matrix v false = A.matrix v false) ∧
      A.matrix false false ^ 2 + A.matrix true false ^ 2 = 0 ∧
      RingHomRealization.mapSignature phi (symmetricGraph N pin).network.denote =
        (fun x => delta * GlobalCloseCompletionIndependentPinsWCore.image R.matrix x) := by
  obtain ⟨a0,a1,aiso,s,t,hs,ht,hB,hC⟩ := common_isotropic_line A B C bc ab ca
  have biso : B.matrix false false ^ 2 + B.matrix true false ^ 2 = 0 := by
    rw [hB,hB]
    linear_combination s ^ 2 * aiso
  have ciso : C.matrix false false ^ 2 + C.matrix true false ^ 2 = 0 := by
    rw [hC,hC]
    linear_combination t ^ 2 * aiso
  have pinFalse : phi (pin.network.denote (fun _ => false)) = c := congrFun zeroPin (fun _ => false)
  have pinTrue : phi (pin.network.denote (fun _ => true)) = 0 := congrFun zeroPin (fun _ => true)
  have rb : B.matrix false false * phi (pin.network.denote (fun _ => false)) +
      B.matrix true false * phi (pin.network.denote (fun _ => true)) ≠ 0 := by
    rw [pinFalse,pinTrue,hB]
    simpa using mul_ne_zero (mul_ne_zero hs a0) hc
  have rc : C.matrix false false * phi (pin.network.denote (fun _ => false)) +
      C.matrix true false * phi (pin.network.denote (fun _ => true)) ≠ 0 := by
    rw [pinFalse,pinTrue,hC]
    simpa using mul_ne_zero (mul_ne_zero ht a0) hc
  let p : Bool → AlgebraicComplex := fun v => phi (pin.network.denote (fun _ => v))
  have db : aligned_scale B.matrix C.matrix p ≠ 0 := mul_ne_zero rc (isotropic_cross_nonzero B biso)
  have dc : aligned_scale C.matrix B.matrix p ≠ 0 := mul_ne_zero rb (isotropic_cross_nonzero C ciso)
  obtain ⟨R,columns,normal⟩ := aligned_normalized A (aligned_scale B.matrix C.matrix p)
    (aligned_scale C.matrix B.matrix p) (aligned_shift B.matrix C.matrix p) (aligned_shift C.matrix B.matrix p) db dc
  exact ⟨R,aligned_scale B.matrix C.matrix p * aligned_scale C.matrix B.matrix p,
    mul_ne_zero db dc,columns,aiso,(symmetricGraph_mapped phi N pin A B C form biso ciso rb rc).trans normal⟩

end Graph
end
end Paper2.Paper1Proved.OddUnary.TernaryW

