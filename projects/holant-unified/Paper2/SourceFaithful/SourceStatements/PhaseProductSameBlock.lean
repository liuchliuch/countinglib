import Paper2.SourceFaithful.SourceStatements.PhaseProductPrimeAssembly

/-! Exact phase-product closure when both contracted ports belong to the same
even two-point block. The empty residual block is its actual scalar. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductClosure
noncomputable section
open Paper2 Tractable HeightOne.PhaseCards
open PhaseProductDecomposition
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

lemma twoPoint_reindex {ι κ : Type} [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (a : ι → Bool) (r : AlgebraicComplex) :
    Tensor.reindex e (twoPoint a r) = twoPoint (fun k => a (e.symm k)) r := by
  funext x
  have he (b : ι → Bool) : (fun i => x (e i)) = b ↔ x = fun k => b (e.symm k) := by
    constructor
    · intro h
      funext k
      have hk := congrFun h (e.symm k)
      simpa using hk
    · intro h
      funext i
      simpa using congrFun h (e i)
  simp only [Tensor.reindex_apply,twoPoint,point,Pi.add_apply,Pi.smul_apply,smul_eq_mul,he]

lemma twoPoint_member_card {N k : ℕ} {I : Type} [Fintype I]
    (hI : Fintype.card I = 2*k) (a : I → Bool) (r : AlgebraicComplex)
    (hr : PhaseRatio N k r) : PhaseProduct N (twoPoint a r) := by
  classical
  cases k with
  | zero =>
    have hi : Fintype.card I = 0 := by simpa using hI
    let : IsEmpty I := Fintype.card_eq_zero_iff.mp hi
    exact phaseProduct_nullary _
  | succ k =>
    let e := (Fintype.equivFin I).symm
    let b : Fin (Fintype.card I) → Bool := fun j => a (e j)
    have hb : EvenPhaseBlock N (twoPoint b r) := ⟨k,b,r,hI,hr,rfl⟩
    have h := (PhaseProduct.of_block hb).reindex e
    rw [twoPoint_reindex] at h
    simpa only [b,e,Equiv.symm_symm,Equiv.symm_apply_apply] using h

theorem same_plus {N k : ℕ} {I : Type} [Fintype I]
    (hI : Fintype.card I = 2*k) (a : I → Bool) (p : Bool → Bool)
    (r : AlgebraicComplex) (hr : PhaseRatio N (k+1) r)
    (s : rootsOfUnity N AlgebraicComplex) :
    PhaseProduct N (contractKernel (plusKernel s.val) (twoPoint (Sum.elim a p) r)) := by
  classical
  cases hp0 : p false <;> cases hp1 : p true
  · have hp : p = fun _ => false := by funext b; cases b <;> assumption
    rw [hp,same_block_plus_false]
    exact twoPoint_member_card hI a _ (hr.delete_pair s)
  · have hp : p false ≠ p true := by simp [hp0,hp1]
    rw [same_block_plus_wrong_xor a p hp]
    exact PhaseProduct.zero N I
  · have hp : p false ≠ p true := by simp [hp0,hp1]
    rw [same_block_plus_wrong_xor a p hp]
    exact PhaseProduct.zero N I
  · have hp : p = fun _ => true := by funext b; cases b <;> assumption
    rw [hp,same_block_plus_true a r s.val (Units.ne_zero s.val)]
    exact (twoPoint_member_card hI a _ (hr.delete_pair_inverse s)).scale _

theorem same_minus {N k : ℕ} {I : Type} [Fintype I]
    (hI : Fintype.card I = 2*k) (a : I → Bool) (p : Bool → Bool)
    (r : AlgebraicComplex) (hr : PhaseRatio N (k+1) r)
    (s : rootsOfUnity N AlgebraicComplex) :
    PhaseProduct N (contractKernel (minusKernel s.val) (twoPoint (Sum.elim a p) r)) := by
  classical
  cases hp0 : p false <;> cases hp1 : p true
  · have hp : p false = p true := by simp [hp0,hp1]
    rw [same_block_minus_wrong_xor a p hp]
    exact PhaseProduct.zero N I
  · have hp : p = fun b => b := by funext b; cases b <;> assumption
    rw [hp,same_block_minus_forward]
    exact twoPoint_member_card hI a _ (hr.delete_pair s)
  · have hp : p = fun b => !b := by funext b; cases b <;> assumption
    rw [hp,same_block_minus_backward a r s.val (Units.ne_zero s.val)]
    exact (twoPoint_member_card hI a _ (hr.delete_pair_inverse s)).scale _
  · have hp : p false = p true := by simp [hp0,hp1]
    rw [same_block_minus_wrong_xor a p hp]
    exact PhaseProduct.zero N I

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductClosure

