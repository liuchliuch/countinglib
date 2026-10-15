import Paper2.Paper1ProvedOddUnaryOneHotBinaryProjectionFactors
import Paper2.Paper1ProvedOddUnaryOneHotBinaryProjectionPolynomial
import Paper2.Paper1ProvedOddUnaryOneHotBinaryProjectionSpecialization
import Holant.Proofs.FiniteGroups.Stabilization.FactorWorklist
import Mathlib.Logic.Equiv.Set

/-! Exact ordered tensor splits reconstructed from disjoint polynomial factors. -/
namespace Paper2.Paper1Proved.OddUnary.OneHotBinaryProjection
open Holant Holant.LocalDrafts.FinitePGL2.Stabilization
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {σ : Type} [Fintype σ]

/-- A factorization on two nonempty complementary port sets is a literal
`ProperSplit`, with an explicit port permutation and scalar one. -/
theorem properSplit_of_tensor_partition {n : ℕ} (e : σ ≃ Fin n)
    (f : Tensor K σ) (s : Set σ) (left : Nonempty s) (right : Nonempty ↥(sᶜ))
    (a : Tensor K s) (b : Tensor K ↥(sᶜ))
    (equation : ∀ x,f x=a (fun i => x i.val)*b (fun i => x i.val)) :
    ∃ a' b' : AnySignature K,
      Nonempty (ProperSplit ⟨n,Tensor.reindex e f⟩ a' b') := by
  classical
  let ea := Fintype.equivFin s
  let eb := Fintype.equivFin ↥(sᶜ)
  let a' : AnySignature K := ⟨Fintype.card s,Tensor.reindex ea a⟩
  let b' : AnySignature K := ⟨Fintype.card ↥(sᶜ),Tensor.reindex eb b⟩
  let ports := ((Equiv.sumCongr ea.symm eb.symm).trans (Equiv.Set.sumCompl s)).trans e
  refine ⟨a',b',⟨{
    left_pos := Fintype.card_pos_iff.mpr left
    right_pos := Fintype.card_pos_iff.mpr right
    ports := ports
    scale := 1
    equation := ?_
  }⟩⟩
  funext x
  simp only [Tensor.reindex,Units.val_one,one_mul]
  rw [equation]
  congr 1
  · congr 1
    funext i
    change x (e i.val)=x (ports (.inl (ea i)))
    simp only [ports,Equiv.trans_apply,Equiv.sumCongr_apply,Sum.map_inl,
      Equiv.symm_apply_apply,Equiv.Set.sumCompl_apply_inl]
  · congr 1
    funext i
    change x (e i.val)=x (ports (.inr (eb i)))
    simp only [ports,Equiv.trans_apply,Equiv.sumCongr_apply,Sum.map_inr,
      Equiv.symm_apply_apply,Equiv.Set.sumCompl_apply_inr]

/-- The coefficient encoding reconstructs the literal tensor product on
two complementary variable sets. -/
theorem tensor_partition_of_polynomial_partition (f : Tensor K σ) (s : Set σ)
    [DecidablePred (·∈s)]
    (a : MvPolynomial s K) (b : MvPolynomial ↥(sᶜ) K)
    (da : ∀ i,MvPolynomial.degreeOf i a≤1)
    (db : ∀ i,MvPolynomial.degreeOf i b≤1)
    (equation : Polynomial.encode f=
      MvPolynomial.rename Subtype.val a*MvPolynomial.rename Subtype.val b) :
    ∀ x,f x=Polynomial.decode a (fun i => x i.val)*
      Polynomial.decode b (fun i => x i.val) := by
  classical
  let product : Tensor K (s ⊕ ↥(sᶜ)) := fun x =>
    Polynomial.decode a (fun i => x (.inl i))*
    Polynomial.decode b (fun i => x (.inr i))
  let ec := Equiv.Set.sumCompl s
  have encoded : Polynomial.encode (Tensor.reindex ec product)=
      MvPolynomial.rename Subtype.val a*MvPolynomial.rename Subtype.val b := by
    change Polynomial.encode (fun x => product (fun i => x (ec i)))=_
    rw [Polynomial.encode_reindex ec product]
    change MvPolynomial.rename ec (Polynomial.encode (fun x =>
      Polynomial.decode a (fun i => x (.inl i))*
      Polynomial.decode b (fun i => x (.inr i))))=_
    rw [Polynomial.encode_tensor_product]
    rw [Polynomial.encode_decode a da,Polynomial.encode_decode b db]
    simp only [map_mul,MvPolynomial.rename_rename,Function.comp_def,
      Equiv.Set.sumCompl_apply_inl,Equiv.Set.sumCompl_apply_inr,ec]
  have tensors : f=Tensor.reindex ec product :=
    Polynomial.encode_injective (equation.trans encoded.symm)
  intro x
  rw [tensors]
  rfl

theorem properSplit_of_polynomial_partition {n : ℕ} (e : σ ≃ Fin n)
    (f : Tensor K σ) (s : Set σ) (left : Nonempty s) (right : Nonempty ↥(sᶜ))
    [DecidablePred (·∈s)]
    (a : MvPolynomial s K) (b : MvPolynomial ↥(sᶜ) K)
    (da : ∀ i,MvPolynomial.degreeOf i a≤1)
    (db : ∀ i,MvPolynomial.degreeOf i b≤1)
    (equation : Polynomial.encode f=
      MvPolynomial.rename Subtype.val a*MvPolynomial.rename Subtype.val b) :
    ∃ a' b' : AnySignature K,
      Nonempty (ProperSplit ⟨n,Tensor.reindex e f⟩ a' b') := by
  exact properSplit_of_tensor_partition e f s left right
    (Polynomial.decode a) (Polynomial.decode b)
    (tensor_partition_of_polynomial_partition f s a b da db equation)

/-- Tensor primality rules out a determinant identity for every fixed pair
of retained ports. The encoding equation fixes all coefficient and port
conventions explicitly. -/
theorem conditional_polynomial_nonsingular {n : ℕ}
    (e : (Bool ⊕ σ) ≃ Fin n) (f : Tensor K (Bool ⊕ σ))
    (prime : Holant.LocalDrafts.FinitePGL2.Stabilization.Prime ⟨n,Tensor.reindex e f⟩)
    (M : Bool → Bool → MvPolynomial σ K)
    (encoding : Polynomial.encode f=twoPortPolynomial M) :
    matrixDeterminantPolynomial M≠0 := by
  classical
  intro singular
  have fnz : f≠0 := by
    intro zero
    apply prime.1
    funext x
    simp only [Tensor.reindex,zero,Pi.zero_apply]
  have pnz : twoPortPolynomial M≠0 := by
    rw [←encoding]
    exact fun zero => fnz ((Polynomial.encode_eq_zero_iff f).mp zero)
  have bounds : ∀ i,MvPolynomial.degreeOf i (twoPortPolynomial M)≤1 := by
    rw [←encoding]
    exact Polynomial.multiaffine_encode f
  obtain ⟨s,h₀,h₁,a,b,equation,da,db⟩ := singular_twoPort_partition M singular pnz bounds
  have left : Nonempty s := ⟨⟨.inl false,h₀⟩⟩
  have right : Nonempty ↥(sᶜ) := ⟨⟨.inl true,h₁⟩⟩
  apply prime.2
  exact properSplit_of_polynomial_partition e f s left right a b da db
    (encoding.trans equation)

end
end Paper2.Paper1Proved.OddUnary.OneHotBinaryProjection

