import Paper2.Paper1ProvedOddUnaryTernarySymmetricW

/-! Physical three-copy W alignment. Every cap and binary insertion uses
the original ordinary dictionary and its equality edges. -/
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

def swap01 : Equiv.Perm (Fin 3) := Equiv.ofBijective (![1,0,2] : Fin 3 → Fin 3) (by decide)
def swap12 : Equiv.Perm (Fin 3) := Equiv.ofBijective (![0,2,1] : Fin 3 → Fin 3) (by decide)
def swap2 : Equiv.Perm (Fin 2) := Equiv.ofBijective (![1,0] : Fin 2 → Fin 2) (by decide)

section Graph
variable {K : Type} [Field K] {r : ℕ} {b : ℕ → ℕ}
variable {H : (i : Fin r) → Signature K (b i.val)}

def transposeMacro (N : Macro H 2) : Macro H 2 := N.reindex swap2
def cap01 (N : Macro H 3) (pin : Macro H 1) : Macro H 2 :=
  GlobalCloseCompletionSymmetricGHZCapGraph.cap (G.rotate N) pin
def cap02 (N : Macro H 3) (pin : Macro H 1) : Macro H 2 :=
  GlobalCloseCompletionSymmetricGHZCapGraph.cap (N.reindex swap01) pin
def decorateLast (N : Macro H 3) (binary : Macro H 2) : Macro H 3 :=
  (D.decorate (N.reindex swap12) binary).reindex swap12
def symmetricGraph (N : Macro H 3) (pin : Macro H 1) : Macro H 3 :=
  decorateLast (D.decorate N (transposeMacro (cap01 N pin))) (transposeMacro (cap02 N pin))

theorem transposeMacro_mapped (phi : K →+* AlgebraicComplex) (N : Macro H 2) (T : Kernel AlgebraicComplex)
    (form : RingHomRealization.mapSignature phi N.network.denote = kernelSignature T) :
    RingHomRealization.mapSignature phi (transposeMacro N).network.denote = kernelSignature (Kernel.transpose T) := by
  funext x
  rw [RingHomRealization.mapSignature,transposeMacro,Macro.reindex_denote]
  have h := congrFun form (fun i => x (swap2 i))
  change phi (N.network.denote (fun i => x (swap2 i))) = _ at h
  change phi (N.network.denote (fun i => x (swap2 i))) = _
  rw [h]
  simp [kernelSignature,swap2,Kernel.transpose]

theorem swap01_image (phi : K →+* AlgebraicComplex) (N : Macro H 3) (A B C : Kernel AlgebraicComplex)
    (form : RingHomRealization.mapSignature phi N.network.denote = W.image A B C) :
    RingHomRealization.mapSignature phi (N.reindex swap01).network.denote = W.image B A C := by
  funext x
  rw [RingHomRealization.mapSignature,Macro.reindex_denote]
  have h := congrFun form (fun i => x (swap01 i))
  change phi (N.network.denote (fun i => x (swap01 i))) = _ at h
  change phi (N.network.denote (fun i => x (swap01 i))) = _
  rw [h]
  simp [W.image,swap01]
  ring

theorem swap12_image (phi : K →+* AlgebraicComplex) (N : Macro H 3) (A B C : Kernel AlgebraicComplex)
    (form : RingHomRealization.mapSignature phi N.network.denote = W.image A B C) :
    RingHomRealization.mapSignature phi (N.reindex swap12).network.denote = W.image A C B := by
  funext x
  rw [RingHomRealization.mapSignature,Macro.reindex_denote]
  have h := congrFun form (fun i => x (swap12 i))
  change phi (N.network.denote (fun i => x (swap12 i))) = _ at h
  change phi (N.network.denote (fun i => x (swap12 i))) = _
  rw [h]
  simp [W.image,swap12]
  ring

theorem cap_first_image (phi : K →+* AlgebraicComplex) (N : Macro H 3) (pin : Macro H 1)
    (A B C : Kernel AlgebraicComplex)
    (form : RingHomRealization.mapSignature phi N.network.denote = W.image A B C) :
    RingHomRealization.mapSignature phi (GlobalCloseCompletionSymmetricGHZCapGraph.cap N pin).network.denote =
      kernelSignature (cap_right B C A (fun v => phi (pin.network.denote (fun _ => v)))) := by
  funext x
  rw [RingHomRealization.mapSignature,GlobalCloseCompletionSymmetricGHZCapGraph.cap_value,map_add,map_mul,map_mul]
  have nf (v : Bool) : phi (N.network.denote ![v,x 0,x 1]) = W.image A B C ![v,x 0,x 1] := congrFun form _
  simp [nf,W.image,kernelSignature,cap_right]
  ring

theorem cap01_mapped (phi : K →+* AlgebraicComplex) (N : Macro H 3) (pin : Macro H 1)
    (A B C : Holant.Tractable.InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote = W.image A.matrix B.matrix C.matrix) :
    RingHomRealization.mapSignature phi (cap01 N pin).network.denote =
      kernelSignature (cap_right A.matrix B.matrix C.matrix (fun v => phi (pin.network.denote (fun _ => v)))) :=
  cap_first_image phi (G.rotate N) pin C.matrix A.matrix B.matrix (rotate_image phi N A B C form)

theorem cap02_mapped (phi : K →+* AlgebraicComplex) (N : Macro H 3) (pin : Macro H 1)
    (A B C : Kernel AlgebraicComplex)
    (form : RingHomRealization.mapSignature phi N.network.denote = W.image A B C) :
    RingHomRealization.mapSignature phi (cap02 N pin).network.denote =
      kernelSignature (cap_right A C B (fun v => phi (pin.network.denote (fun _ => v)))) :=
  cap_first_image phi (N.reindex swap01) pin B A C (swap01_image phi N A B C form)

theorem decorateLast_image (phi : K →+* AlgebraicComplex) (N : Macro H 3) (binary : Macro H 2)
    (A B C T : Holant.Tractable.InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote = W.image A.matrix B.matrix C.matrix)
    (binaryForm : RingHomRealization.mapSignature phi binary.network.denote = kernelSignature T.matrix) :
    RingHomRealization.mapSignature phi (decorateLast N binary).network.denote =
      W.image A.matrix B.matrix ((Transpose.transpose T).comp C).matrix := by
  have first := swap12_image phi N A.matrix B.matrix C.matrix form
  have second := decorate_image phi (N.reindex swap12) binary A C B T first binaryForm
  exact swap12_image phi (D.decorate (N.reindex swap12) binary) A.matrix
    ((Transpose.transpose T).comp C).matrix B.matrix second

theorem symmetricGraph_mapped (phi : K →+* AlgebraicComplex) (N : Macro H 3) (pin : Macro H 1)
    (A B C : Holant.Tractable.InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote = W.image A.matrix B.matrix C.matrix)
    (biso : B.matrix false false ^ 2 + B.matrix true false ^ 2 = 0)
    (ciso : C.matrix false false ^ 2 + C.matrix true false ^ 2 = 0)
    (rb : B.matrix false false * phi (pin.network.denote (fun _ => false)) +
      B.matrix true false * phi (pin.network.denote (fun _ => true)) ≠ 0)
    (rc : C.matrix false false * phi (pin.network.denote (fun _ => false)) +
      C.matrix true false * phi (pin.network.denote (fun _ => true)) ≠ 0) :
    RingHomRealization.mapSignature phi (symmetricGraph N pin).network.denote =
      aligned_value A.matrix
        (aligned_scale B.matrix C.matrix (fun v => phi (pin.network.denote (fun _ => v))))
        (aligned_scale C.matrix B.matrix (fun v => phi (pin.network.denote (fun _ => v))))
        (aligned_shift B.matrix C.matrix (fun v => phi (pin.network.denote (fun _ => v))))
        (aligned_shift C.matrix B.matrix (fun v => phi (pin.network.denote (fun _ => v)))) := by
  let p : Bool → AlgebraicComplex := fun v => phi (pin.network.denote (fun _ => v))
  have det01 : SymmetricBinaryPullback.determinant (cap_right A.matrix B.matrix C.matrix p) ≠ 0 := by
    change cap_right A.matrix B.matrix C.matrix p false false * cap_right A.matrix B.matrix C.matrix p true true -
      cap_right A.matrix B.matrix C.matrix p false true * cap_right A.matrix B.matrix C.matrix p true false ≠ 0
    rw [cap_determinant]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ rc))
      (SymmetricBinaryPullback.determinant_ne_zero A)) (SymmetricBinaryPullback.determinant_ne_zero B)
  have det02 : SymmetricBinaryPullback.determinant (cap_right A.matrix C.matrix B.matrix p) ≠ 0 := by
    change cap_right A.matrix C.matrix B.matrix p false false * cap_right A.matrix C.matrix B.matrix p true true -
      cap_right A.matrix C.matrix B.matrix p false true * cap_right A.matrix C.matrix B.matrix p true false ≠ 0
    rw [cap_determinant]
    exact mul_ne_zero (mul_ne_zero (neg_ne_zero.mpr (pow_ne_zero _ rb))
      (SymmetricBinaryPullback.determinant_ne_zero A)) (SymmetricBinaryPullback.determinant_ne_zero C)
  let T01 := SymmetricBinaryPullback.invertibleOfDeterminant (cap_right A.matrix B.matrix C.matrix p) det01
  let T02 := SymmetricBinaryPullback.invertibleOfDeterminant (cap_right A.matrix C.matrix B.matrix p) det02
  let B' := (Transpose.transpose (Transpose.transpose T01)).comp B
  let C' := (Transpose.transpose (Transpose.transpose T02)).comp C
  have first : RingHomRealization.mapSignature phi (D.decorate N (transposeMacro (cap01 N pin))).network.denote =
      W.image A.matrix B'.matrix C.matrix :=
    decorate_image phi N (transposeMacro (cap01 N pin)) A B C (Transpose.transpose T01) form
      (transposeMacro_mapped phi (cap01 N pin) T01.matrix (cap01_mapped phi N pin A B C form))
  have second : RingHomRealization.mapSignature phi (symmetricGraph N pin).network.denote =
      W.image A.matrix B'.matrix C'.matrix :=
    decorateLast_image phi (D.decorate N (transposeMacro (cap01 N pin))) (transposeMacro (cap02 N pin))
      A B' C (Transpose.transpose T02) first
      (transposeMacro_mapped phi (cap02 N pin) T02.matrix (cap02_mapped phi N pin A.matrix B.matrix C.matrix form))
  have hb := cap_alignment A.matrix B.matrix C.matrix p biso
  have hc := cap_alignment A.matrix C.matrix B.matrix p ciso
  exact second.trans (image_aligned A.matrix B'.matrix C'.matrix _ _ _ _ hb.1 hb.2 hc.1 hc.2)

end Graph
end
end Paper2.Paper1Proved.OddUnary.TernaryW

