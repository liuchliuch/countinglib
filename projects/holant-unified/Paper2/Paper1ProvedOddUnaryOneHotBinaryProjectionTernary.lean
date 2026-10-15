import Paper2.Paper1ProvedOddUnaryOneHotBinaryProjectionPencil
import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsTernaryRankOne
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4PrimeTools

/-! A prime ternary has a nonsingular ordinary binary projection. Both the
cap coefficients and the final simultaneous 11-entry specialization stay
in the original infinite coefficient field. Algebraic-complex orbit
classification proves nonvanishing, then coefficient descent selects the
original-field cap. -/
namespace Paper2.Paper1Proved.OddUnary.OneHotBinaryProjection
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384

variable {K : Type} [Field K]

def ternaryCap (f : Holant.Signature K 3) (u : Bool → K) : Bool → Bool → K :=
  fun i j => ∑ v : Bool,u v*f ![v,i,j]

theorem ternaryCap_combination (f : Holant.Signature K 3) (u : Bool → K) :
    ternaryCap f u=combination (fun i j => f ![false,i,j])
      (fun i j => f ![true,i,j]) (u false) (u true) := by
  funext i j
  simp only [ternaryCap,combination,Fintype.sum_bool]
  ring

private def dualRow (A : InvertibleKernel) (v : Bool → AlgebraicComplex) : Bool → AlgebraicComplex :=
  fun i => v false*A.inverse false i+v true*A.inverse true i

private theorem dualRow_pair (A : InvertibleKernel) (v : Bool → AlgebraicComplex) (b : Bool) :
    (∑ i : Bool,dualRow A v i*A.matrix i b)=v b := by
  have h0 := congrFun₂ A.inverse_matrix false b
  have h1 := congrFun₂ A.inverse_matrix true b
  simp only [Kernel.mul_apply] at h0 h1
  simp only [dualRow,Fintype.sum_bool]
  cases b <;> simp only [Signature.equality,Bool.false_eq_true,Bool.true_eq_false,
    ite_false,ite_true] at h0 h1
  all_goals linear_combination v false*h0+v true*h1

private theorem cap_ghz (A B C : InvertibleKernel) (v : Bool → AlgebraicComplex) :
    ternaryCap (GlobalCloseCompletionTernaryGHZCore.ghz A.matrix B.matrix C.matrix)
      (dualRow A v)=fun i j =>
        v false*B.matrix i false*C.matrix j false+v true*B.matrix i true*C.matrix j true := by
  funext i j
  have h0 := dualRow_pair A v false
  have h1 := dualRow_pair A v true
  simp only [Fintype.sum_bool] at h0 h1
  simp only [ternaryCap,GlobalCloseCompletionTernaryGHZCore.ghz,Fintype.sum_bool,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  linear_combination (B.matrix i false*C.matrix j false)*h0+
    (B.matrix i true*C.matrix j true)*h1

private theorem cap_w (A B C : InvertibleKernel) (v : Bool → AlgebraicComplex) :
    ternaryCap (GlobalCloseCompletionIndependentPinsWGeneralCore.image A.matrix B.matrix C.matrix)
      (dualRow A v)=fun i j =>
        v true*B.matrix i false*C.matrix j false+
          v false*B.matrix i true*C.matrix j false+
          v false*B.matrix i false*C.matrix j true := by
  funext i j
  have h0 := dualRow_pair A v false
  have h1 := dualRow_pair A v true
  simp only [Fintype.sum_bool] at h0 h1
  simp only [ternaryCap,GlobalCloseCompletionIndependentPinsWGeneralCore.image,Fintype.sum_bool,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  linear_combination (B.matrix i true*C.matrix j false+B.matrix i false*C.matrix j true)*h0+
    (B.matrix i false*C.matrix j false)*h1

/-- This is a proved nonvanishing conclusion from actual ternary primality. -/
theorem ternary_nonsingular_complex (f : Holant.Signature AlgebraicComplex 3)
    (prime : Prime (⟨3,f⟩ : Holant.AnySignature AlgebraicComplex)) :
    ∃ u : Bool → AlgebraicComplex,determinant (ternaryCap f u)≠0 := by
  rcases GlobalCloseCompletionIndependentPinsTernaryRankOne.decomposition f prime with
    ⟨A,B,C,rfl⟩|⟨A,B,C,rfl⟩
  · refine ⟨dualRow A (fun _ => 1),?_⟩
    rw [cap_ghz]
    have formula : determinant (fun i j =>
        (1 : AlgebraicComplex)*B.matrix i false*C.matrix j false+
          1*B.matrix i true*C.matrix j true)=
        SymmetricBinaryPullback.determinant B.matrix*SymmetricBinaryPullback.determinant C.matrix := by
      simp only [determinant,SymmetricBinaryPullback.determinant]
      ring
    rw [formula]
    exact mul_ne_zero (SymmetricBinaryPullback.determinant_ne_zero B)
      (SymmetricBinaryPullback.determinant_ne_zero C)
  · refine ⟨dualRow A (fun i => if i then 0 else 1),?_⟩
    rw [cap_w]
    simp only [Bool.false_eq_true,ite_false,ite_true,zero_mul,zero_add,one_mul]
    have formula : determinant (fun i j =>
        B.matrix i true*C.matrix j false+B.matrix i false*C.matrix j true)=
        -(SymmetricBinaryPullback.determinant B.matrix*SymmetricBinaryPullback.determinant C.matrix) := by
      simp only [determinant,SymmetricBinaryPullback.determinant]
      ring
    rw [formula]
    exact neg_ne_zero.mpr (mul_ne_zero (SymmetricBinaryPullback.determinant_ne_zero B)
      (SymmetricBinaryPullback.determinant_ne_zero C))

/-- Nonvanishing descends to original coefficients; no orbit coefficient
is installed as a graph label or as a cap. -/
theorem ternary_nonsingular_original (phi : K →+* AlgebraicComplex)
    (f : Holant.Signature K 3)
    (prime : Prime (⟨3,RingHomRealization.mapSignature phi f⟩ : Holant.AnySignature AlgebraicComplex)) :
    ∃ u : Bool → K,determinant (ternaryCap f u)≠0 := by
  obtain ⟨u,live⟩ := ternary_nonsingular_complex (RingHomRealization.mapSignature phi f) prime
  have mapped : ∃ a b : AlgebraicComplex,determinant
      (combination (fun i j => phi (f ![false,i,j])) (fun i j => phi (f ![true,i,j])) a b)≠0 := by
    refine ⟨u false,u true,?_⟩
    rw [ternaryCap_combination] at live
    exact live
  obtain ⟨a,b,live⟩ := descend_nonsingular phi
    (fun i j => f ![false,i,j]) (fun i j => f ![true,i,j]) mapped
  refine ⟨(fun v => if v then b else a),?_⟩
  rw [ternaryCap_combination]
  simpa only [Bool.false_eq_true,ite_false,ite_true] using live

/-- A specified live weight-two face of a prime ternary admits a cap in
the unchanged field with both a live 11 entry and a nonzero determinant. -/
theorem ternary_face_projection [Infinite K] (phi : K →+* AlgebraicComplex)
    (f : Holant.Signature K 3)
    (prime : Prime (⟨3,RingHomRealization.mapSignature phi f⟩ : Holant.AnySignature AlgebraicComplex))
    (face : ∃ v : Bool,f ![v,true,true]≠0) :
    ∃ u : Bool → K,ternaryCap f u true true≠0 ∧ determinant (ternaryCap f u)≠0 := by
  obtain ⟨u,live⟩ := ternary_nonsingular_original phi f prime
  have nonsingular : ∃ a b,determinant
      (combination (fun i j => f ![false,i,j]) (fun i j => f ![true,i,j]) a b)≠0 := by
    refine ⟨u false,u true,?_⟩
    rwa [ternaryCap_combination] at live
  have entry : f ![false,true,true]≠0 ∨ f ![true,true,true]≠0 := by
    obtain ⟨v,live⟩ := face
    cases v
    · exact Or.inl live
    · exact Or.inr live
  obtain ⟨z,entry,det⟩ := select_pencil _ _ entry nonsingular
  refine ⟨(fun v => if v then z else 1),?_,?_⟩
  all_goals rw [ternaryCap_combination]
  · simpa only [Bool.false_eq_true,ite_false,ite_true] using entry
  · simpa only [Bool.false_eq_true,ite_false,ite_true] using det

/-- A fixed linear measurement visible on a literal face remains visible
on a nonsingular projection, with a cap from the original field. -/
theorem ternary_linear_projection [Infinite K] (phi : K →+* AlgebraicComplex)
    (f : Holant.Signature K 3)
    (prime : Prime (⟨3,RingHomRealization.mapSignature phi f⟩ : Holant.AnySignature AlgebraicComplex))
    (L : (Bool → Bool → K) →ₗ[K] K)
    (visible : ∃ v : Bool,L (fun i j => f ![v,i,j])≠0) :
    ∃ u : Bool → K,L (ternaryCap f u)≠0 ∧ determinant (ternaryCap f u)≠0 := by
  obtain ⟨u,live⟩ := ternary_nonsingular_original phi f prime
  have nonsingular : ∃ a b,determinant
      (combination (fun i j => f ![false,i,j]) (fun i j => f ![true,i,j]) a b)≠0 := by
    refine ⟨u false,u true,?_⟩
    rwa [ternaryCap_combination] at live
  have entry : L (fun i j => f ![false,i,j])≠0 ∨ L (fun i j => f ![true,i,j])≠0 := by
    obtain ⟨v,live⟩ := visible
    cases v
    · exact Or.inl live
    · exact Or.inr live
  obtain ⟨z,entry,det⟩ := select_pencil_linear _ _ L entry nonsingular
  refine ⟨(fun v => if v then z else 1),?_,?_⟩
  all_goals rw [ternaryCap_combination]
  · simpa only [Bool.false_eq_true,ite_false,ite_true] using entry
  · simpa only [Bool.false_eq_true,ite_false,ite_true] using det

/-- A non-one-hot ternary has a literal live two-port face after a
permutation of its original ports. -/
theorem ternary_live_face (f : Holant.Signature K 3) (outside : ¬Holant.Signature.OneHot f) :
    ∃ p : Equiv.Perm (Fin 3),∃ v : Bool,(Tensor.reindex p f) ![v,true,true]≠0 := by
  classical
  by_contra bad
  push Not at bad
  have h011 : f ![false,true,true]=0 := by
    simpa only [Tensor.reindex_refl] using bad (Equiv.refl _) false
  have h111 : f ![true,true,true]=0 := by
    simpa only [Tensor.reindex_refl] using bad (Equiv.refl _) true
  have h101 : f ![true,false,true]=0 := by
    have h := bad (Equiv.swap (0 : Fin 3) 1) false
    change f (fun i => (![false,true,true] : Fin 3 → Bool) (Equiv.swap 0 1 i))=0 at h
    have word : (fun i => (![false,true,true] : Fin 3 → Bool) (Equiv.swap 0 1 i))=![true,false,true] := by
      funext i
      fin_cases i <;> decide
    rwa [word] at h
  have h110 : f ![true,true,false]=0 := by
    have h := bad (Equiv.swap (0 : Fin 3) 2) false
    change f (fun i => (![false,true,true] : Fin 3 → Bool) (Equiv.swap 0 2 i))=0 at h
    have word : (fun i => (![false,true,true] : Fin 3 → Bool) (Equiv.swap 0 2 i))=![true,true,false] := by
      funext i
      fin_cases i <;> decide
    rwa [word] at h
  apply outside
  intro x weight
  have word : x=![x 0,x 1,x 2] := by
    funext i
    fin_cases i <;> rfl
  rw [word]
  simp only [Holant.weight,Fin.sum_univ_three] at weight
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [h0,h1,h2] at weight
  · exact h011
  · exact h101
  · exact h110
  · exact h111

/-- Complete ternary projection from primality and literal failure of the
one-hot condition. The port permutation and the original-field cap are
both selected internally. -/
theorem ternary_projection [Infinite K] (phi : K →+* AlgebraicComplex)
    (f : Holant.Signature K 3)
    (prime : Prime (⟨3,RingHomRealization.mapSignature phi f⟩ : Holant.AnySignature AlgebraicComplex))
    (outside : ¬Holant.Signature.OneHot f) :
    ∃ p : Equiv.Perm (Fin 3),∃ u : Bool → K,
      ternaryCap (Tensor.reindex p f) u true true≠0 ∧
        determinant (ternaryCap (Tensor.reindex p f) u)≠0 := by
  obtain ⟨p,v,live⟩ := ternary_live_face f outside
  have reindexed : RingHomRealization.mapSignature phi (Tensor.reindex p f)=
      Tensor.reindex p (RingHomRealization.mapSignature phi f) := rfl
  have retainedPrime : Prime
      (⟨3,RingHomRealization.mapSignature phi (Tensor.reindex p f)⟩ : Holant.AnySignature AlgebraicComplex) := by
    rw [reindexed]
    exact GlobalCloseCompletionC2Q4PrimeTools.prime_reindex _ prime p
  obtain ⟨u,entry,det⟩ := ternary_face_projection phi (Tensor.reindex p f) retainedPrime ⟨v,live⟩
  exact ⟨p,u,entry,det⟩

end
end Paper2.Paper1Proved.OddUnary.OneHotBinaryProjection

