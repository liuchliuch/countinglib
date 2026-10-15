import Paper2.Paper1ProvedOddUnaryTernaryBinary

/-! Two actual capped copies align the three columns of an isotropic W
tensor. Their common excitation coefficients give a symmetric W output. -/
namespace Paper2.Paper1Proved.OddUnary.TernaryW
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open OrdinaryNegativeCubicGadgets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384

section Algebra
variable {K : Type} [Field K]

def cap_right (A B C : Kernel K) (p : Bool → K) : Kernel K := fun i j =>
  (A i true * B j false + A i false * B j true) *
    (C false false * p false + C true false * p true) +
  A i false * B j false * (C false true * p false + C true true * p true)

def cross (B : Kernel K) : K := B false false * B false true + B true false * B true true

def aligned_scale (B C : Kernel K) (p : Bool → K) : K :=
  (C false false * p false + C true false * p true) * cross B

def aligned_shift (B C : Kernel K) (p : Bool → K) : K :=
  (C false false * p false + C true false * p true) * (B false true ^ 2 + B true true ^ 2) +
  (C false true * p false + C true true * p true) * cross B

theorem cap_alignment (A B C : Kernel K) (p : Bool → K)
    (isotropic : B false false ^ 2 + B true false ^ 2 = 0) :
    (∀ v, Kernel.mul (cap_right A B C p) B v false = aligned_scale B C p * A v false) ∧
    (∀ v, Kernel.mul (cap_right A B C p) B v true =
      aligned_scale B C p * A v true + aligned_shift B C p * A v false) := by
  constructor
  · intro v
    simp only [Kernel.mul_apply,cap_right,aligned_scale,cross]
    linear_combination ((C false false * p false + C true false * p true) * A v true +
      (C false true * p false + C true true * p true) * A v false) * isotropic
  · intro v
    simp only [Kernel.mul_apply,cap_right,aligned_scale,aligned_shift,cross]
    ring

theorem cap_determinant (A B C : Kernel K) (p : Bool → K) :
    cap_right A B C p false false * cap_right A B C p true true -
      cap_right A B C p false true * cap_right A B C p true false =
      -(C false false * p false + C true false * p true) ^ 2 *
        (A false false * A true true - A false true * A true false) *
        (B false false * B true true - B false true * B true false) := by
  simp only [cap_right]
  ring

def aligned_value (A : Kernel K) (db dc eb ec : K) : Signature K 3 := fun x =>
  db * dc * GlobalCloseCompletionIndependentPinsWCore.image A x +
    (eb * dc + db * ec) * A (x 0) false * A (x 1) false * A (x 2) false

theorem image_aligned (A B C : Kernel K) (db dc eb ec : K)
    (b0 : ∀ v, B v false = db * A v false)
    (b1 : ∀ v, B v true = db * A v true + eb * A v false)
    (c0 : ∀ v, C v false = dc * A v false)
    (c1 : ∀ v, C v true = dc * A v true + ec * A v false) :
    W.image A B C = aligned_value A db dc eb ec := by
  funext x
  simp only [W.image,b0,b1,c0,c1,aligned_value,GlobalCloseCompletionIndependentPinsWCore.image]
  ring

theorem aligned_symmetric (A : Kernel K) (db dc eb ec : K) :
    aligned_value A db dc eb ec = GlobalCloseCompletionTernaryGHZSymmetry.symmetric
      (GlobalCloseCompletionTernaryGHZSymmetry.values (aligned_value A db dc eb ec)) := by
  apply GlobalCloseCompletionTernaryGHZSymmetry.of_cyclic
  intro x
  simp only [aligned_value,GlobalCloseCompletionIndependentPinsWCore.image,GlobalCloseCompletionTernaryGHZCore.cyclic]
  simp
  ring

end Algebra

theorem isotropic_cross_nonzero (B : Holant.Tractable.InvertibleKernel)
    (isotropic : B.matrix false false ^ 2 + B.matrix true false ^ 2 = 0) : cross B.matrix ≠ 0 := by
  intro zero
  have det := GlobalCloseCompletionIndependentPinsWCore.gram_determinant (1 : AlgebraicComplex) B.matrix
  simp only [GlobalCloseCompletionIndependentPinsWCore.gram,one_mul] at det
  change B.matrix false false * B.matrix false true + B.matrix true false * B.matrix true true = 0 at zero
  have square : (SymmetricBinaryPullback.determinant B.matrix) ^ 2 = 0 := by
    simpa [←pow_two,isotropic,zero,SymmetricBinaryPullback.determinant] using det.symm
  exact (SymmetricBinaryPullback.determinant_ne_zero B) (sq_eq_zero_iff.mp square)

end
end Paper2.Paper1Proved.OddUnary.TernaryW

