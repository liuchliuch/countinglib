import Paper2.PrimeFactorization
import Paper2.ChargeBridgeNetwork

/-! Explicit normalized unary factors of a nonzero scaled pure point mass. -/
namespace Paper2
open Tractable ExactInput
open scoped BigOperators

namespace TensorDecomposition

/-- The literal unary pin, as a one-port signature. -/
noncomputable def literalPin (b : Bool) : Signature AlgebraicComplex 1 :=
  fun x => if x 0 = b then 1 else 0

@[simp] theorem literalPin_const (b : Bool) : literalPin b (fun _ => b) = 1 := by
  simp [literalPin]

theorem literalPin_ne_zero (b : Bool) : literalPin b ≠ 0 := by
  intro h
  have := congrFun h (fun _ => b)
  simp at this

theorem literalPin_prime (b : Bool) : TensorPrime (literalPin b) :=
  unary_tensorPrime _ (literalPin_ne_zero b)

/-- The nonzero scalar is stored in `scale`; all n factors are the exact unit
unary pin, so factor extraction obtains literal pins without normalization. -/
noncomputable def pointMass (b : Bool) (n : ℕ) (c : AlgebraicComplex) (hc : c ≠ 0) :
    TensorDecomposition AlgebraicComplex n where
  count := n
  arity := fun _ => 1
  factor := fun _ => literalPin b
  ports :=
    { toFun := fun p => p.1
      invFun := fun i => ⟨i, 0⟩
      left_inv := by rintro ⟨i, j⟩; have : j = 0 := Fin.eq_zero j; subst j; rfl
      right_inv := fun _ => rfl }
  scale := Units.mk0 c hc

theorem value_pointMass (b : Bool) (n : ℕ) (c : AlgebraicComplex) (hc : c ≠ 0) :
    (pointMass b n c hc).value = ChargeBridge.pointMass b n c := by
  funext x
  change c * (∏ i : Fin n, if x i = b then (1 : AlgebraicComplex) else 0) =
    if x = (fun _ => b) then c else 0
  rw [Fintype.prod_boole]
  by_cases h : x = (fun _ => b)
  · subst x
    simp
  · have h' : ¬ ∀ i, x i = b := fun hi => h (funext hi)
    simp [h, h']

@[simp] theorem pointMass_positive (b : Bool) (n : ℕ) (c : AlgebraicComplex) (hc : c ≠ 0)
    (i : Fin (pointMass b n c hc).count) : 0 < (pointMass b n c hc).arity i := by
  exact Nat.zero_lt_one

theorem pointMass_prime (b : Bool) (n : ℕ) (c : AlgebraicComplex) (hc : c ≠ 0)
    (i : Fin (pointMass b n c hc).count) : TensorPrime ((pointMass b n c hc).factor i) :=
  literalPin_prime b

/-- On positive arity, one of the recorded prime factors is the literal pin. -/
theorem pointMass_has_literalPin (b : Bool) {n : ℕ} (hn : 0 < n)
    (c : AlgebraicComplex) (hc : c ≠ 0) :
    ∃ i : Fin (pointMass b n c hc).count,
      (⟨(pointMass b n c hc).arity i, (pointMass b n c hc).factor i⟩ :
        AnySignature AlgebraicComplex) = ⟨1, literalPin b⟩ :=
  ⟨⟨0, hn⟩, rfl⟩

end TensorDecomposition
/-- A nonzero pure point mass of positive arity yields a literal pin in a
retained exact-input augmentation via the separately accepted Paper 1 lemma. -/
theorem pointMass_factorClosure (P : Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    (b : Bool) {n : ℕ} (hn : 0 < n) (c : AlgebraicComplex) (hc : c ≠ 0)
    (hmem : (⟨n, ChargeBridge.pointMass b n c⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ M : Language, L.family ⊆ M.family ∧
      (⟨1, TensorDecomposition.literalPin b⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      Preprocessed M.family ∧ ¬ CommonOneSided M.family ∧
      Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M := by
  obtain ⟨M, hsub, hfactors, hpre, hside, hML, hLM⟩ :=
    factorClosure_with_member_decomposition P L hL htwo _ hmem
      (TensorDecomposition.pointMass b n c hc)
      (TensorDecomposition.value_pointMass b n c hc)
      (TensorDecomposition.pointMass_positive b n c hc)
      (TensorDecomposition.pointMass_prime b n c hc)
  exact ⟨M, hsub, hfactors ⟨0, hn⟩, hpre, hside, hML, hLM⟩

/-- Both pure point masses yield both literal pins, with actual machine
reductions composed through two retained factor augmentations. -/
theorem pointMass_pair_factorClosure (P : Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n)
    (c d : AlgebraicComplex) (hc : c ≠ 0) (hd : d ≠ 0)
    (hzero : (⟨m, ChargeBridge.pointMass false m c⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hone : (⟨n, ChargeBridge.pointMass true n d⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ M : Language, L.family ⊆ M.family ∧
      (⟨1, TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      (⟨1, TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      Preprocessed M.family ∧ ¬ CommonOneSided M.family ∧
      Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M := by
  obtain ⟨A, hLA, hz, hpreA, hsideA, hAL, hLAred⟩ :=
    pointMass_factorClosure P L hL htwo false hm c hc hzero
  obtain ⟨M, hAM, ho, hpreM, hsideM, hMA, hAMred⟩ :=
    pointMass_factorClosure P A hpreA hsideA true hn d hd (hLA hone)
  exact ⟨M, hLA.trans hAM, hAM hz, ho, hpreM, hsideM,
    hMA.trans hAL, hLAred.trans hAMred⟩

end Paper2
