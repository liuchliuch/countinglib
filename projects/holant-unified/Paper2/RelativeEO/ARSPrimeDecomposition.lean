import Paper2.RelativeEO.ARSFactors
import Paper2.PrimeFactorization

/-! Constructive finite existence of genuine algebraic EO/projective-ARS prime
factor decompositions. The induction is the actual nontrivial port split of
TensorPrime; no factor-divisibility or ARS-factorization theorem is assumed. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
open Paper2.Tractable

theorem exists_prime_eoARS_decomposition {n : ℕ} (f : Signature AlgebraicComplex n)
    (hn : 0 < n) (hf : f ≠ 0) (he : Signature.CentralSupport f) (hs : ProjectiveARS f) :
    ∃ D : TensorDecomposition AlgebraicComplex n, D.value = f ∧
      (∀ i, 0 < D.arity i) ∧ (∀ i, TensorPrime (D.factor i)) ∧
      (∀ i, Signature.CentralSupport (D.factor i)) ∧
      (∀ i, ProjectiveARS (D.factor i)) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hp : TensorPrime f
    · exact ⟨TensorDecomposition.singleton f,TensorDecomposition.value_singleton f,
        fun _ => hn,fun _ => hp,fun _ => he,fun _ => hs⟩
    · simp only [TensorPrime] at hp
      push Not at hp
      obtain ⟨m,k,hm,hk,e,a,b,hab⟩ := hp hf
      have hcard : m+k=n := by simpa using Fintype.card_congr e
      have ha : a ≠ 0 := by
        intro hz
        apply hf
        rw [← hab,hz]
        funext x
        simp [Tensor.reindex,Signature.tensor,Tensor.tensor]
      have hb : b ≠ 0 := by
        intro hz
        apply hf
        rw [← hab,hz]
        funext x
        simp [Tensor.reindex,Signature.tensor,Tensor.tensor]
      have hsab : ProjectiveARS (Signature.tensor a b) := by
        have hh := hs.reindex e.symm
        rw [← hab,Tensor.reindex_symm] at hh
        exact hh
      have heab : Signature.CentralSupport (Signature.tensor a b) := by
        have hh := centralSupport_reindex he e.symm
        rw [← hab,Tensor.reindex_symm] at hh
        exact hh
      obtain ⟨hea,heb⟩ := tensor_factors_central a b ha hb heab hsab
      obtain ⟨hsa,hsb⟩ := tensor_factors_projectiveARS a b ha hb hsab
      obtain ⟨A,hA,hAp,hAt,hAe,hAs⟩ := ih m (by omega) a hm ha hea hsa
      obtain ⟨B,hB,hBp,hBt,hBe,hBs⟩ := ih k (by omega) b hk hb heb hsb
      refine ⟨(A.append B).reindex e,?_,?_,?_,?_,?_⟩
      · rw [TensorDecomposition.value_reindex,TensorDecomposition.value_append,hA,hB]
        exact hab
      · exact TensorDecomposition.factors_append A B (fun r _ => 0 < r) hAp hBp
      · exact TensorDecomposition.factors_append A B (fun _ g => TensorPrime g) hAt hBt
      · exact TensorDecomposition.factors_append A B (fun _ g => Signature.CentralSupport g) hAe hBe
      · exact TensorDecomposition.factors_append A B (fun _ g => ProjectiveARS g) hAs hBs

/-- A genuine nonzero EO factor has even arity, not just an even-arity parent. -/
theorem even_arity_of_nonzero_central {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : f ≠ 0) (he : Signature.CentralSupport f) : ∃ d, n = 2*d := by
  classical
  obtain ⟨x,hx⟩ : ∃ x, f x ≠ 0 := by by_contra h; push Not at h; exact hf (funext h)
  refine ⟨weight x,?_⟩
  by_contra hn
  exact hx (he x (Ne.symm hn))

/-- Nonzero rescaling preserves actual tensor primality. -/
theorem tensorPrime_scale {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : TensorPrime f) (c : AlgebraicComplex) (hc : c ≠ 0) :
    TensorPrime (fun x => c*f x) := by
  refine ⟨?_,?_⟩
  · intro hz
    apply hf.1
    funext x
    have hh := congrFun hz x
    exact (mul_eq_zero.mp hh).resolve_left hc
  · intro m k hm hk e a b he
    apply hf.2 m k hm hk e (fun x => c⁻¹*a x) b
    funext x
    have hh := congrFun he x
    change a (fun i => x (e (Fin.castAdd k i))) * b (fun j => x (e (Fin.natAdd m j))) = c*f x at hh
    change (c⁻¹ * a (fun i => x (e (Fin.castAdd k i)))) * b (fun j => x (e (Fin.natAdd m j))) = f x
    rw [mul_assoc,hh,← mul_assoc,inv_mul_cancel₀ hc,one_mul]

/-- Exact ARS representatives stay algebraic and prime. This is a coefficient
normalization; actual language access is recorded in a separate graph theorem. -/
theorem exact_ARS_representative {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : TensorPrime f) (he : Signature.CentralSupport f) (hs : ProjectiveARS f) :
    ∃ (c : AlgebraicComplex) (g : Signature AlgebraicComplex n), c ≠ 0 ∧
      f = (fun x => c*g x) ∧ TensorPrime g ∧ Signature.CentralSupport g ∧ ARS g := by
  obtain ⟨c,hc,hs⟩ := hs
  let g := fun x => c⁻¹*f x
  refine ⟨c,g,hc,?_,tensorPrime_scale f hf c⁻¹ (inv_ne_zero hc),?_,?_⟩
  · funext x
    dsimp [g]
    rw [← mul_assoc,mul_inv_cancel₀ hc,one_mul]
  · intro x hx
    simp only [g,he x hx,mul_zero]
  · exact hs

end Paper2.RelativeEO
