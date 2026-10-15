import Paper2.Paper1ProvedOddUnaryOneHotBinaryProjectionFactorSplit
import Paper2.Paper1ProvedOddUnaryOneHotBinaryProjectionPairEncoding
import Holant.Proofs.FiniteGroups.Stabilization.FactorBaseChange

/-! Product-covector binary projection with the last two ports retained. -/
namespace Paper2.Paper1Proved.OddUnary.OneHotBinaryProjection
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {K : Type} [Field K]

def lastTwoOrder (n : ℕ) : (Bool ⊕ Fin n) ≃ Fin (n+2) :=
  ((Equiv.sumCongr finTwoEquiv.symm (Equiv.refl (Fin n))).trans
    (Equiv.sumComm (Fin 2) (Fin n))).trans finSumFinEquiv

@[simp] theorem lastTwoOrder_inl (n : ℕ) (b : Bool) :
    lastTwoOrder n (.inl b)=Fin.natAdd n (finTwoEquiv.symm b) := by
  simp [lastTwoOrder]

@[simp] theorem lastTwoOrder_inr (n : ℕ) (i : Fin n) :
    lastTwoOrder n (.inr i)=Fin.castAdd 2 i := by
  simp [lastTwoOrder]

private theorem lastTwoOrder_join {n : ℕ} (y : Fin n → Bool) (i j : Bool) :
    (fun k : Fin (n+2) =>
      Sum.elim (fun b => if b then j else i) y ((lastTwoOrder n).symm k))=
    Fin.append y ![i,j] := by
  funext k
  obtain ⟨k,rfl⟩ := (lastTwoOrder n).surjective k
  rw [Equiv.symm_apply_apply]
  cases k with
  | inl b =>
      rw [lastTwoOrder_inl,Fin.append_right]
      cases b <;> rfl
  | inr i => rw [lastTwoOrder_inr,Fin.append_left]; rfl

def lastPairMatrixPolynomial {n : ℕ} (f : Signature K (n+2)) :
    Bool → Bool → MvPolynomial (Fin n) K :=
  fun i j => Polynomial.encode (fun y => f (Fin.append y ![i,j]))

/-- The literal product of the covectors `[1,z_i]` leaves the last two
ordered ports open. Every Boolean assignment is included. -/
def orderedProductProjection {n : ℕ} (f : Signature K (n+2))
    (z : Fin n → K) : Bool → Bool → K :=
  fun i j => ∑ y : Fin n → Bool,
    (∏ k : Fin n,if y k then z k else 1)*f (Fin.append y ![i,j])

theorem eval_lastPairMatrixPolynomial {n : ℕ} (f : Signature K (n+2))
    (z : Fin n → K) (i j : Bool) :
    MvPolynomial.eval z (lastPairMatrixPolynomial f i j)=
      orderedProductProjection f z i j := by
  classical
  rw [lastPairMatrixPolynomial,Polynomial.eval_encode]
  apply Finset.sum_congr rfl
  intro y _
  rw [mul_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  cases y k <;> simp

/-- Every prescribed pair of ports of a prime tensor has a nonzero
conditional determinant polynomial. -/
theorem last_pair_polynomial_nonsingular {n : ℕ} (f : Signature K (n+2))
    (prime : Holant.LocalDrafts.FinitePGL2.Stabilization.Prime ⟨n+2,f⟩) :
    matrixDeterminantPolynomial (lastPairMatrixPolynomial f)≠0 := by
  classical
  let e := lastTwoOrder n
  let fs := Tensor.reindex e.symm f
  have primed : Holant.LocalDrafts.FinitePGL2.Stabilization.Prime
      ⟨n+2,Tensor.reindex e fs⟩ := by
    have same : Tensor.reindex e fs=f := by
      simpa only [fs,Equiv.symm_symm] using Tensor.reindex_symm e.symm f
    rw [same]
    exact prime
  apply conditional_polynomial_nonsingular e fs primed (lastPairMatrixPolynomial f)
  rw [encode_twoPort_matrix]
  congr 1
  funext i j
  congr 1
  funext y
  change f (fun k => Sum.elim (fun b => if b then j else i) y (e.symm k))=
    f (Fin.append y ![i,j])
  rw [lastTwoOrder_join]

/-- Over the original infinite field, product covectors can simultaneously
make the retained binary nonsingular and preserve any visible linear
expression. The covectors are literally `[1,z_i]`. -/
theorem last_two_linear_projection [Infinite K] {n : ℕ}
    (f : Signature K (n+2))
    (prime : Holant.LocalDrafts.FinitePGL2.Stabilization.Prime ⟨n+2,f⟩)
    (w : Bool → Bool → K)
    (visible : ∃ y : Fin n → Bool,
      (∑ i : Bool,∑ j : Bool,w i j*f (Fin.append y ![i,j]))≠0) :
    ∃ z : Fin n → K,
      determinant (orderedProductProjection f z)≠0 ∧
      (∑ i : Bool,∑ j : Bool,w i j*orderedProductProjection f z i j)≠0 := by
  classical
  obtain ⟨y,live⟩ := visible
  have nonsingular := last_pair_polynomial_nonsingular f prime
  have livePolynomial : matrixVisiblePolynomial w (lastPairMatrixPolynomial f)≠0 := by
    apply matrixVisiblePolynomial_nonzero
    refine ⟨Polynomial.exponent y,?_⟩
    simpa only [lastPairMatrixPolynomial,Polynomial.encode_coeff_word] using live
  obtain ⟨z,det,line⟩ := select_polynomial_matrix
    (lastPairMatrixPolynomial f) w nonsingular livePolynomial
  refine ⟨z,?_,?_⟩
  · simpa only [eval_lastPairMatrixPolynomial] using det
  · simpa only [eval_lastPairMatrixPolynomial] using line

theorem last_two_entry_projection [Infinite K] {n : ℕ}
    (f : Signature K (n+2))
    (prime : Holant.LocalDrafts.FinitePGL2.Stabilization.Prime ⟨n+2,f⟩)
    (visible : ∃ y : Fin n → Bool,f (Fin.append y ![true,true])≠0) :
    ∃ z : Fin n → K,orderedProductProjection f z true true≠0 ∧
      determinant (orderedProductProjection f z)≠0 := by
  classical
  let w : Bool → Bool → K := fun i j => if i=true ∧ j=true then 1 else 0
  have lineVisible : ∃ y : Fin n → Bool,
      (∑ i : Bool,∑ j : Bool,w i j*f (Fin.append y ![i,j]))≠0 := by
    obtain ⟨y,live⟩ := visible
    exact ⟨y,by simpa [w,Fintype.sum_bool] using live⟩
  obtain ⟨z,det,line⟩ := last_two_linear_projection f prime w lineVisible
  exact ⟨z,by simpa [w,Fintype.sum_bool] using line,det⟩

end
end Paper2.Paper1Proved.OddUnary.OneHotBinaryProjection

