import Paper2.Paper1ProvedOddUnaryTernaryLine
import Holant.Proofs.Hardness.GeneralOddNonisotropicFrame

/-! An ordinary self-loop of one of three cyclic copies of an isotropic W
macro gives a nonzero isotropic unary in the same original table. All edges,
labels and boundary incidences are retained by the actual macro operations. -/
namespace Paper2.Paper1Proved.OddUnary.WTrace
open Holant Holant.Algebraic Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open OrdinaryNegativeCubicGadgets
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev traceScalar (A B : Kernel AlgebraicComplex) : AlgebraicComplex :=
  TernaryW.W.gram 1 A B true false + TernaryW.W.gram 1 A B false true

/-- The literal ordinary loop contracts the first two W ports. -/
theorem contract_image {K : Type} [Field K] {r : ℕ} {b : ℕ → ℕ}
    {H : (i : Fin r) → Signature K (b i.val)}
    (phi : K →+* AlgebraicComplex) (N : Macro H 3)
    (A B C : InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote =
      TernaryW.W.image A.matrix B.matrix C.matrix)
    (ab : TernaryW.W.gram (1 : AlgebraicComplex) A.matrix B.matrix false false = 0) :
    RingHomRealization.mapSignature phi N.contract.network.denote =
      fun x => traceScalar A.matrix B.matrix * C.matrix (x 0) false := by
  funext x
  rw [RingHomRealization.mapSignature,Macro.contract_denote,map_add]
  have h0 := congrFun form (Fin.cons false (Fin.cons false x))
  have h1 := congrFun form (Fin.cons true (Fin.cons true x))
  change phi (N.network.denote (Fin.cons false (Fin.cons false x))) = _ at h0
  change phi (N.network.denote (Fin.cons true (Fin.cons true x))) = _ at h1
  rw [h0,h1]
  simp only [TernaryW.W.image,Fin.cons_zero,Fin.cons_one]
  simp only [TernaryW.W.gram,one_mul] at ab
  dsimp [traceScalar,TernaryW.W.gram]
  linear_combination C.matrix (x 0) true * ab

/-- At least one cyclic ordinary loop has nonzero scalar on the common
isotropic line. Three vanishing loops would kill an invertible column pair. -/
theorem cyclic_trace_nonzero (A B C : InvertibleKernel)
    (bc : TernaryW.W.gram (1 : AlgebraicComplex) B.matrix C.matrix false false = 0)
    (ab : TernaryW.W.gram 1 A.matrix B.matrix false false = 0)
    (ca : TernaryW.W.gram 1 C.matrix A.matrix false false = 0) :
    ∃ s t : AlgebraicComplex, s ≠ 0 ∧ t ≠ 0 ∧
      (∀ v, B.matrix v false = s * A.matrix v false) ∧
      (∀ v, C.matrix v false = t * A.matrix v false) ∧
      A.matrix false false ≠ 0 ∧ A.matrix true false ≠ 0 ∧
      A.matrix false false ^ 2 + A.matrix true false ^ 2 = 0 ∧
      (t * traceScalar A.matrix B.matrix ≠ 0 ∨
        s * traceScalar C.matrix A.matrix ≠ 0 ∨ traceScalar B.matrix C.matrix ≠ 0) := by
  obtain ⟨a0,a1,iso,s,t,hs,ht,hB,hC⟩ := TernaryW.common_isotropic_line A B C bc ab ca
  refine ⟨s,t,hs,ht,hB,hC,a0,a1,iso,?_⟩
  have det := SymmetricBinaryPullback.determinant_ne_zero A
  have dot : TernaryW.W.gram (1 : AlgebraicComplex) A.matrix A.matrix true false ≠ 0 := by
    intro hz
    have he : A.matrix false false * TernaryW.W.gram (1 : AlgebraicComplex) A.matrix A.matrix true false =
        A.matrix true false * SymmetricBinaryPullback.determinant A.matrix := by
      simp only [TernaryW.W.gram,one_mul,SymmetricBinaryPullback.determinant]
      linear_combination A.matrix false true * iso
    rw [hz,mul_zero] at he
    exact (mul_ne_zero a1 det) he.symm
  by_contra no
  push Not at no
  have nAB : traceScalar A.matrix B.matrix = 0 := (mul_eq_zero.mp no.1).resolve_left ht
  have nCA : traceScalar C.matrix A.matrix = 0 := (mul_eq_zero.mp no.2.1).resolve_left hs
  have nBC := no.2.2
  have he : (2 : AlgebraicComplex) * s * t *
      TernaryW.W.gram (1 : AlgebraicComplex) A.matrix A.matrix true false = 0 := by
    simp only [traceScalar,TernaryW.W.gram,one_mul] at nAB nCA nBC ⊢
    rw [hB false,hB true] at nAB
    rw [hC false,hC true] at nCA
    rw [hB false,hB true,hC false,hC true] at nBC
    linear_combination t * nAB + s * nCA - nBC
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hs) ht) dot) he

private theorem line_unary {K : Type} [Field K] {r : ℕ} {b : ℕ → ℕ}
    {H : (i : Fin r) → Signature K (b i.val)}
    (phi : K →+* AlgebraicComplex) (Q : Macro H 1) (A : InvertibleKernel)
    (d : AlgebraicComplex) (hd : d ≠ 0)
    (a0 : A.matrix false false ≠ 0) (a1 : A.matrix true false ≠ 0)
    (iso : A.matrix false false ^ 2 + A.matrix true false ^ 2 = 0)
    (form : RingHomRealization.mapSignature phi Q.network.denote =
      fun x => d * A.matrix (x 0) false) :
    Q.network.denote (fun _ => false) ≠ 0 ∧
      Q.network.denote (fun _ => true) ≠ 0 ∧ GeneralOddNonisotropicFrame.norm Q.network.denote = 0 := by
  have h0 : phi (Q.network.denote (fun _ => false)) = d * A.matrix false false := congrFun form _
  have h1 : phi (Q.network.denote (fun _ => true)) = d * A.matrix true false := congrFun form _
  refine ⟨?_,?_,?_⟩
  · intro hz
    rw [hz,map_zero] at h0
    exact mul_ne_zero hd a0 h0.symm
  · intro hz
    rw [hz,map_zero] at h1
    exact mul_ne_zero hd a1 h1.symm
  · apply phi.injective
    simp only [GeneralOddNonisotropicFrame.norm,map_add,map_pow,map_zero]
    rw [h0,h1]
    linear_combination d^2 * iso

/-- An explicit same-table macro is nonzero in both entries and isotropic.
The proof chooses only a genuine self-loop or one of its cyclic rotations. -/
theorem trace_isotropic_unary {K : Type} [Field K] {r : ℕ} {b : ℕ → ℕ}
    {H : (i : Fin r) → Signature K (b i.val)}
    (phi : K →+* AlgebraicComplex) (N : Macro H 3)
    (A B C : InvertibleKernel)
    (form : RingHomRealization.mapSignature phi N.network.denote =
      TernaryW.W.image A.matrix B.matrix C.matrix)
    (bc : TernaryW.W.gram (1 : AlgebraicComplex) B.matrix C.matrix false false = 0)
    (ab : TernaryW.W.gram 1 A.matrix B.matrix false false = 0)
    (ca : TernaryW.W.gram 1 C.matrix A.matrix false false = 0) :
    ∃ Q : Macro H 1, Q.network.denote (fun _ => false) ≠ 0 ∧
      Q.network.denote (fun _ => true) ≠ 0 ∧ GeneralOddNonisotropicFrame.norm Q.network.denote = 0 := by
  obtain ⟨s,t,hs,ht,hB,hC,a0,a1,iso,good⟩ := cyclic_trace_nonzero A B C bc ab ca
  rcases good with good | good | good
  · refine ⟨N.contract,?_⟩
    apply line_unary phi N.contract A (t * traceScalar A.matrix B.matrix) good a0 a1 iso
    rw [contract_image phi N A B C form ab]
    funext x
    rw [hC (x 0)]
    ring
  · let Q := TernaryW.G.rotate N
    have formQ := TernaryW.rotate_image phi N A B C form
    refine ⟨Q.contract,?_⟩
    apply line_unary phi Q.contract A (s * traceScalar C.matrix A.matrix) good a0 a1 iso
    rw [contract_image phi Q C A B formQ ca]
    funext x
    rw [hB (x 0)]
    ring
  · let Q := TernaryW.G.rotate (TernaryW.G.rotate N)
    have formQ := TernaryW.rotate_image phi (TernaryW.G.rotate N) C A B
      (TernaryW.rotate_image phi N A B C form)
    refine ⟨Q.contract,?_⟩
    exact line_unary phi Q.contract A (traceScalar B.matrix C.matrix) good a0 a1 iso
      (contract_image phi Q B C A formQ bc)

/-- Direct specialization to the actual residual packet. -/
theorem residual_unary {r : ℕ} {b : ℕ → ℕ}
    (K : IntermediateField ℚ AlgebraicComplex)
    (H : (i : Fin r) → Signature K (b i.val))
    (h : TernaryW.IsotropicWResidual K H) :
    ∃ Q : Macro H 1, Q.network.denote (fun _ => false) ≠ 0 ∧
      Q.network.denote (fun _ => true) ≠ 0 ∧ GeneralOddNonisotropicFrame.norm Q.network.denote = 0 := by
  obtain ⟨N,A,B,C,form,bc,ab,ca⟩ := h
  exact trace_isotropic_unary K.subtype N A B C form bc ab ca

end
end Paper2.Paper1Proved.OddUnary.WTrace
