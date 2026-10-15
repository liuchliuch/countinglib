import Paper2.Paper1Accepted
import Paper2.Mountain

/-! Structural part of the height-two argument. A proper factorization of an
even-parity quaternary table with both nonzero endpoints consists of two
nonsingular weighted equalities. This is a table theorem; factor extraction and
whole-family basis transport remain computational steps. -/
namespace Paper2.HeightTwo

variable {K ι κ : Type*}

/-- Literal even Hamming parity, with zero tables allowed. -/
def EvenSupport [Fintype ι] [Zero K] (f : Tensor K ι) : Prop :=
  ∀ x, f x ≠ 0 → Even (weight x)

lemma EvenSupport.reindex [Fintype ι] [Fintype κ] [Zero K]
    {f : Tensor K ι} (h : EvenSupport f) (e : ι ≃ κ) :
    EvenSupport (Tensor.reindex e f) := by
  intro x hx
  simpa only [weight_reindex] using h (fun i => x (e i)) hx

lemma evenSupport_reindex_iff [Fintype ι] [Fintype κ] [Zero K]
    (e : ι ≃ κ) (f : Tensor K ι) :
    EvenSupport (Tensor.reindex e f) ↔ EvenSupport f := by
  constructor
  · intro h
    simpa only [Tensor.reindex_symm] using h.reindex e.symm
  · exact fun h => h.reindex e

lemma factor_evenSupport [Fintype ι] [Fintype κ]
    [MulZeroClass K] [NoZeroDivisors K]
    (A : Tensor K ι) (B : Tensor K κ)
    (h : EvenSupport (Tensor.tensor A B))
    (hA0 : A (fun _ => false) ≠ 0) (hB0 : B (fun _ => false) ≠ 0) :
    EvenSupport A ∧ EvenSupport B := by
  constructor
  · intro x hx
    have he := h (Sum.elim x (fun _ => false)) (mul_ne_zero hx hB0)
    simpa only [weight_sum, weight_false, add_zero] using he
  · intro x hx
    have he := h (Sum.elim (fun _ => false) x) (mul_ne_zero hA0 hx)
    simpa only [weight_sum, weight_false, zero_add] using he

lemma even_arity_of_endpoints [Fintype ι] [Zero K] (f : Tensor K ι)
    (h : EvenSupport f) (hend : f (fun _ => true) ≠ 0) : Even (Fintype.card ι) := by
  simpa only [weight_true] using h (fun _ => true) hend

/-- Actual diagonal truth table with two independently retained nonzero values. -/
def WeightedEquality [Zero K] (f : Signature K 2) : Prop :=
  f ![false, true] = 0 ∧ f ![true, false] = 0 ∧
    f ![false, false] ≠ 0 ∧ f ![true, true] ≠ 0

lemma weightedEquality_of_even [Zero K] (f : Signature K 2)
    (h : EvenSupport f) (h0 : f (fun _ => false) ≠ 0)
    (h1 : f (fun _ => true) ≠ 0) : WeightedEquality f := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · by_contra hx
    have he := h ![false, true] hx
    have hw : weight ![false, true] = 1 := by decide
    rw [hw] at he
    norm_num at he
  · by_contra hx
    have he := h ![true, false] hx
    have hw : weight ![true, false] = 1 := by decide
    rw [hw] at he
    norm_num at he
  · have heq : ![false, false] = (fun _ : Fin 2 => false) := by
      funext i; fin_cases i <;> rfl
    simpa only [heq] using h0
  · have heq : ![true, true] = (fun _ : Fin 2 => true) := by
      funext i; fin_cases i <;> rfl
    simpa only [heq] using h1

/-- No odd-arity factor can occur: tensor independence and the two endpoint
coefficients force each factor to have even support and positive even arity. -/
theorem proper_split_arities [CommSemiring K] [NoZeroDivisors K]
    {m n : ℕ} (A : Signature K m) (B : Signature K n)
    (e : Fin (m + n) ≃ Fin 4) (hm : 0 < m) (hn : 0 < n)
    (h : EvenSupport (Tensor.reindex e (Signature.tensor A B)))
    (h0 : Tensor.reindex e (Signature.tensor A B) (fun _ => false) ≠ 0)
    (h1 : Tensor.reindex e (Signature.tensor A B) (fun _ => true) ≠ 0) :
    m = 2 ∧ n = 2 ∧ EvenSupport A ∧ EvenSupport B := by
  have ht : EvenSupport (Tensor.tensor A B) := by
    apply (evenSupport_reindex_iff finSumFinEquiv _).mp
    exact (evenSupport_reindex_iff e _).mp h
  have hAz : A (fun _ => false) ≠ 0 := left_ne_zero_of_mul h0
  have hBz : B (fun _ => false) ≠ 0 := right_ne_zero_of_mul h0
  have hAo : A (fun _ => true) ≠ 0 := left_ne_zero_of_mul h1
  have hBo : B (fun _ => true) ≠ 0 := right_ne_zero_of_mul h1
  obtain ⟨hA, hB⟩ := factor_evenSupport A B ht hAz hBz
  have hmEven : Even m := by simpa using even_arity_of_endpoints A hA hAo
  have hnEven : Even n := by simpa using even_arity_of_endpoints B hB hBo
  have hcard : m + n = 4 := by simpa using Fintype.card_congr e
  obtain ⟨a, ha⟩ := hmEven
  obtain ⟨b, hb⟩ := hnEven
  exact ⟨by omega, by omega, hA, hB⟩

/-- In the resulting 2+2 split, both literal factor tables are nonsingular
weighted equalities, not arbitrary binary signatures. -/
theorem binary_factors_weightedEqualities [CommSemiring K] [NoZeroDivisors K]
    (A B : Signature K 2) (e : Fin (2 + 2) ≃ Fin 4)
    (h : EvenSupport (Tensor.reindex e (Signature.tensor A B)))
    (h0 : Tensor.reindex e (Signature.tensor A B) (fun _ => false) ≠ 0)
    (h1 : Tensor.reindex e (Signature.tensor A B) (fun _ => true) ≠ 0) :
    WeightedEquality A ∧ WeightedEquality B := by
  obtain ⟨_, _, hA, hB⟩ := proper_split_arities A B e (by omega) (by omega) h h0 h1
  exact ⟨weightedEquality_of_even A hA (left_ne_zero_of_mul h0) (left_ne_zero_of_mul h1),
    weightedEquality_of_even B hB (right_ne_zero_of_mul h0) (right_ne_zero_of_mul h1)⟩

/-- Every height-two mountain has exactly the parity hypothesis of the
source prime eight-vertex theorem. -/
theorem mountain_evenSupport [Zero K] (f : Signature K 4)
    (h : IsMountain (d := 2) f) : EvenSupport f := by
  intro x hx
  rcases h.support_layers x hx with hz | hc | ho
  · subst x
    simp only [weight_false]
    decide
  · have hw : weight x = 2 := (halfCharge_eq_zero_iff (d := 2) x).mp hc
    rw [hw]
    decide
  · subst x
    simp only [weight_true, Fintype.card_fin]
    decide

/-- Exhaustive algebraic case split for the height-two proof: primality, or
an actual ordered 2+2 factorization into nonsingular weighted equalities. -/
theorem prime_or_weightedEquality_product (f : Signature Tractable.AlgebraicComplex 4)
    (h : EvenSupport f) (h0 : f (fun _ => false) ≠ 0)
    (h1 : f (fun _ => true) ≠ 0) :
    TensorPrime f ∨ ∃ (A B : Signature Tractable.AlgebraicComplex 2)
      (e : Fin (2 + 2) ≃ Fin 4),
      Tensor.reindex e (Signature.tensor A B) = f ∧
      WeightedEquality A ∧ WeightedEquality B := by
  classical
  by_cases hp : TensorPrime f
  · exact Or.inl hp
  · right
    have hf : f ≠ 0 := by
      intro he
      exact h0 (congrFun he _)
    have hsplit : ¬ (∀ m k, 0 < m → 0 < k → ∀ e : Fin (m + k) ≃ Fin 4,
        ∀ a : Signature Tractable.AlgebraicComplex m,
          ∀ b : Signature Tractable.AlgebraicComplex k,
            Tensor.reindex e (Signature.tensor a b) ≠ f) := by
      exact fun hs => hp ⟨hf, hs⟩
    push Not at hsplit
    obtain ⟨m, n, hm, hn, e, A, B, he⟩ := hsplit
    have hh : EvenSupport (Tensor.reindex e (Signature.tensor A B)) := he ▸ h
    have hz : Tensor.reindex e (Signature.tensor A B) (fun _ => false) ≠ 0 := by
      simpa only [he] using h0
    have ho : Tensor.reindex e (Signature.tensor A B) (fun _ => true) ≠ 0 := by
      simpa only [he] using h1
    obtain ⟨rfl, rfl, _, _⟩ := proper_split_arities A B e hm hn hh hz ho
    exact ⟨A, B, e, he, binary_factors_weightedEqualities A B e hh hz ho⟩

/-- The mountain's tensor-prime branch supplies the exact accepted statement's
literal input, rather than assuming an eight-vertex classification. -/
theorem prime_mountain_classification (P : Paper1Accepted) (L : ExactInput.Language)
    (f : Signature Tractable.AlgebraicComplex 4)
    (hmem : (⟨4, f⟩ : AnySignature Tractable.AlgebraicComplex) ∈ L.family)
    (hm : IsMountain (d := 2) f) (hp : TensorPrime f) :
    (Tractable.Tract (kImage L) → Problem.InFP .nativeX L) ∧
    (¬ Tractable.Tract (kImage L) → Problem.SharpPHard .nativeX L) := by
  apply P.primeQuaternaryDichotomy_2_24 L
  refine ⟨f, hmem, hp, ?_, mul_ne_zero hm.zero_ne_zero hm.one_ne_zero⟩
  intro x hx
  by_contra hn
  obtain ⟨a, ha⟩ := mountain_evenSupport f hm x hn
  obtain ⟨b, hb⟩ := hx
  omega

end Paper2.HeightTwo
