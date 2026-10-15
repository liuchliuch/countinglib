import Paper2.ExactInput.FactorClosure

/-! Actual existence of finite ordered tensor-prime decompositions. -/
namespace Paper2
open Tractable ExactInput
open scoped BigOperators

namespace TensorDecomposition

variable {K : Type*} [CommMonoid K] {m n : ℕ}

/-- Enumerate a finite index type without losing any ordered factor port. -/
noncomputable def ofFinite {I : Type*} [Fintype I]
    (r : I → ℕ) (f : (i : I) → Signature K (r i))
    (p : (Σ i : I, Fin (r i)) ≃ Fin n) (c : Kˣ) : TensorDecomposition K n where
  count := Fintype.card I
  arity := fun i => r ((Fintype.equivFin I).symm i)
  factor := fun i => f ((Fintype.equivFin I).symm i)
  ports := (Equiv.sigmaCongrLeft (Fintype.equivFin I).symm).trans p
  scale := c

theorem value_ofFinite {I : Type*} [Fintype I]
    (r : I → ℕ) (f : (i : I) → Signature K (r i))
    (p : (Σ i : I, Fin (r i)) ≃ Fin n) (c : Kˣ) (x : Fin n → Bool) :
    (ofFinite r f p c).value x =
      (c : K) * ∏ i : I, f i (fun j => x (p ⟨i, j⟩)) := by
  change (c : K) * (∏ i : Fin (Fintype.card I),
    f ((Fintype.equivFin I).symm i) (fun j => x (p ⟨(Fintype.equivFin I).symm i, j⟩))) = _
  exact congrArg (fun z => (c : K) * z)
    ((Fintype.equivFin I).symm.prod_comp (fun i => f i (fun j => x (p ⟨i, j⟩))))

/-- A single factor, retaining the original port ordering and unit scale. -/
def singleton (f : Signature K n) : TensorDecomposition K n where
  count := 1
  arity := fun _ => n
  factor := fun _ => f
  ports :=
    { toFun := fun p => p.2
      invFun := fun j => ⟨0, j⟩
      left_inv := by rintro ⟨i, j⟩; have : i = 0 := Fin.eq_zero i; subst i; rfl
      right_inv := fun _ => rfl }
  scale := 1

@[simp] theorem value_singleton (f : Signature K n) : (singleton f).value = f := by
  funext x
  change (1 : K) * (∏ _i : Fin 1, f x) = f x
  simp

/-- Concatenate decompositions over the two disjoint ordered blocks. -/
noncomputable def append (A : TensorDecomposition K m) (B : TensorDecomposition K n) :
    TensorDecomposition K (m + n) :=
  ofFinite (Sum.elim A.arity B.arity)
    (fun i => match i with | .inl a => A.factor a | .inr b => B.factor b)
    (((Equiv.sumSigmaDistrib (fun i => Fin (Sum.elim A.arity B.arity i))).trans
      (Equiv.sumCongr A.ports B.ports)).trans finSumFinEquiv)
    (A.scale * B.scale)

theorem value_append (A : TensorDecomposition K m) (B : TensorDecomposition K n) :
    (A.append B).value = Signature.tensor A.value B.value := by
  funext x
  rw [append, value_ofFinite, Fintype.prod_sum_type]
  simp only [Units.val_mul, Equiv.trans_apply, Equiv.sumSigmaDistrib_apply,
    Signature.tensor_apply, value]
  ac_rfl

/-- Reorder only the external ports; the factor data and scalar are unchanged. -/
def reindex (A : TensorDecomposition K m) (e : Fin m ≃ Fin n) :
    TensorDecomposition K n :=
  { A with ports := A.ports.trans e }

@[simp] theorem value_reindex (A : TensorDecomposition K m) (e : Fin m ≃ Fin n) :
    (A.reindex e).value = Tensor.reindex e A.value := rfl

/-- Any property of all factors survives concatenation. -/
theorem factors_append (A : TensorDecomposition K m) (B : TensorDecomposition K n)
    (P : (r : ℕ) → Signature K r → Prop)
    (hA : ∀ i, P (A.arity i) (A.factor i))
    (hB : ∀ i, P (B.arity i) (B.factor i)) :
    ∀ i, P ((A.append B).arity i) ((A.append B).factor i) := by
  intro i
  change P (Sum.elim A.arity B.arity ((Fintype.equivFin (Fin A.count ⊕ Fin B.count)).symm i))
    (match (Fintype.equivFin (Fin A.count ⊕ Fin B.count)).symm i with
      | .inl a => A.factor a
      | .inr b => B.factor b)
  cases h : (Fintype.equivFin (Fin A.count ⊕ Fin B.count)).symm i with
  | inl a => simpa only [h, Sum.elim_inl] using hA a
  | inr b => simpa only [h, Sum.elim_inr] using hB b

/-- Locate an original left factor after finite re-enumeration. -/
noncomputable def appendIndexLeft (A : TensorDecomposition K m) (B : TensorDecomposition K n)
    (i : Fin A.count) : Fin (A.append B).count :=
  (Fintype.equivFin (Fin A.count ⊕ Fin B.count)) (.inl i)

/-- Locate an original right factor after finite re-enumeration. -/
noncomputable def appendIndexRight (A : TensorDecomposition K m) (B : TensorDecomposition K n)
    (i : Fin B.count) : Fin (A.append B).count :=
  (Fintype.equivFin (Fin A.count ⊕ Fin B.count)) (.inr i)

theorem append_factor_left (A : TensorDecomposition K m) (B : TensorDecomposition K n)
    (i : Fin A.count) :
    (⟨(A.append B).arity (A.appendIndexLeft B i),
      (A.append B).factor (A.appendIndexLeft B i)⟩ : AnySignature K) =
      ⟨A.arity i, A.factor i⟩ := by
  exact congrArg (fun z : Fin A.count ⊕ Fin B.count =>
    (⟨Sum.elim A.arity B.arity z,
      match z with | .inl a => A.factor a | .inr b => B.factor b⟩ : AnySignature K))
    ((Fintype.equivFin (Fin A.count ⊕ Fin B.count)).symm_apply_apply (.inl i))

theorem append_factor_right (A : TensorDecomposition K m) (B : TensorDecomposition K n)
    (i : Fin B.count) :
    (⟨(A.append B).arity (A.appendIndexRight B i),
      (A.append B).factor (A.appendIndexRight B i)⟩ : AnySignature K) =
      ⟨B.arity i, B.factor i⟩ := by
  exact congrArg (fun z : Fin A.count ⊕ Fin B.count =>
    (⟨Sum.elim A.arity B.arity z,
      match z with | .inl a => A.factor a | .inr b => B.factor b⟩ : AnySignature K))
    ((Fintype.equivFin (Fin A.count ⊕ Fin B.count)).symm_apply_apply (.inr i))

end TensorDecomposition

/-- Every nonzero positive-arity table has an actual ordered tensor-prime
factorization. No prime-factor or Paper 2 structural theorem is assumed. -/
theorem exists_prime_decomposition {n : ℕ} (f : Signature AlgebraicComplex n)
    (hn : 0 < n) (hf : f ≠ 0) :
    ∃ D : TensorDecomposition AlgebraicComplex n,
      D.value = f ∧ (∀ i, 0 < D.arity i) ∧ (∀ i, TensorPrime (D.factor i)) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hp : TensorPrime f
    · exact ⟨TensorDecomposition.singleton f, TensorDecomposition.value_singleton f,
        fun _ => hn, fun _ => hp⟩
    · simp only [TensorPrime] at hp
      push Not at hp
      obtain ⟨m, k, hm, hk, e, a, b, hab⟩ := hp hf
      have hcard : m + k = n := by simpa using Fintype.card_congr e
      have ha : a ≠ 0 := by
        intro hz
        apply hf
        rw [← hab, hz]
        funext x
        simp [Tensor.reindex, Signature.tensor, Tensor.tensor]
      have hb : b ≠ 0 := by
        intro hz
        apply hf
        rw [← hab, hz]
        funext x
        simp [Tensor.reindex, Signature.tensor, Tensor.tensor]
      obtain ⟨A, hA, hAp, hAt⟩ := ih m (by omega) a hm ha
      obtain ⟨B, hB, hBp, hBt⟩ := ih k (by omega) b hk hb
      refine ⟨(A.append B).reindex e, ?_, ?_, ?_⟩
      · rw [TensorDecomposition.value_reindex, TensorDecomposition.value_append, hA, hB]
        exact hab
      · exact TensorDecomposition.factors_append A B (fun r _ => 0 < r) hAp hBp
      · exact TensorDecomposition.factors_append A B (fun _ g => TensorPrime g) hAt hBt

namespace PrimeFactorization

/-- The semantic preprocessing condition supplies exactly the two hypotheses
needed for genuine prime decomposition of every finite exact-input label. -/
theorem nonempty_of_preprocessed (L : Language) (hL : Preprocessed L.family) :
    Nonempty (PrimeFactorization L) := by
  classical
  have hex : ∀ i : Fin L.count, ∃ D : TensorDecomposition AlgebraicComplex (L.arity i.val),
      D.value = L.signature i ∧ (∀ j, 0 < D.arity j) ∧
        (∀ j, TensorPrime (D.factor j)) := by
    intro i
    have hi := hL ⟨L.arity i.val, L.signature i⟩ ⟨i, rfl⟩
    exact exists_prime_decomposition _ hi.1 hi.2
  choose D hval hpos hprime using hex
  exact ⟨⟨D, hval, hpos, hprime⟩⟩

/-- Choose actual ordered factors only after discarding zero/nullary signatures. -/
noncomputable def ofPreprocessed (L : Language) (hL : Preprocessed L.family) :
    PrimeFactorization L := Classical.choice (nonempty_of_preprocessed L hL)

/-- Replace one label's factorization by a specified genuine decomposition.
The scalar and all ordered port data of that decomposition are kept exactly. -/
noncomputable def replace {L : Language} (D : PrimeFactorization L) (i : Fin L.count)
    (Q : TensorDecomposition AlgebraicComplex (L.arity i.val))
    (hQ : Q.value = L.signature i) (hp : ∀ j, 0 < Q.arity j)
    (ht : ∀ j, TensorPrime (Q.factor j)) : PrimeFactorization L := by
  classical
  let pack : (j : Fin L.count) →
      { Q : TensorDecomposition AlgebraicComplex (L.arity j.val) //
        Q.value = L.signature j ∧ (∀ k, 0 < Q.arity k) ∧
          (∀ k, TensorPrime (Q.factor k)) } :=
    fun j => ⟨D.decomposition j, D.exact_value j, D.positive j, D.prime j⟩
  let upd := Function.update pack i ⟨Q, hQ, hp, ht⟩
  exact ⟨fun j => (upd j).1, fun j => (upd j).2.1,
    fun j => (upd j).2.2.1, fun j => (upd j).2.2.2⟩

@[simp] theorem replace_decomposition {L : Language} (D : PrimeFactorization L)
    (i : Fin L.count) (Q : TensorDecomposition AlgebraicComplex (L.arity i.val))
    (hQ : Q.value = L.signature i) (hp : ∀ j, 0 < Q.arity j)
    (ht : ∀ j, TensorPrime (Q.factor j)) :
    (D.replace i Q hQ hp ht).decomposition i = Q := by
  classical
  simp [replace]

/-- Choose a full language factorization that uses a prescribed decomposition
at one exact input index, making all of its factors actual family members. -/
theorem exists_with_decomposition (L : Language) (hL : Preprocessed L.family)
    (i : Fin L.count) (Q : TensorDecomposition AlgebraicComplex (L.arity i.val))
    (hQ : Q.value = L.signature i) (hp : ∀ j, 0 < Q.arity j)
    (ht : ∀ j, TensorPrime (Q.factor j)) :
    ∃ D : PrimeFactorization L, D.decomposition i = Q ∧
      ∀ j, (⟨Q.arity j, Q.factor j⟩ : AnySignature AlgebraicComplex) ∈ D.factors := by
  let D := (ofPreprocessed L hL).replace i Q hQ hp ht
  have hD : D.decomposition i = Q := replace_decomposition _ _ _ _ _ _
  refine ⟨D, hD, ?_⟩
  rw [← hD]
  intro j
  exact ⟨⟨i, j⟩, rfl⟩

/-- The member-level interface avoids requiring a client to select or transport
an exact input index. Every factor of the specified decomposition is retained. -/
theorem exists_with_member_decomposition (L : Language) (hL : Preprocessed L.family)
    {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : (⟨n, f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (Q : TensorDecomposition AlgebraicComplex n) (hQ : Q.value = f)
    (hp : ∀ j, 0 < Q.arity j) (ht : ∀ j, TensorPrime (Q.factor j)) :
    ∃ D : PrimeFactorization L,
      ∀ j, (⟨Q.arity j, Q.factor j⟩ : AnySignature AlgebraicComplex) ∈ D.factors := by
  obtain ⟨i, hi⟩ := hf
  have hn : L.arity i.val = n := congrArg Sigma.fst hi
  cases hn
  have hfi : L.signature i = f := eq_of_heq (Sigma.mk.inj_iff.mp hi).2
  obtain ⟨D, _, hall⟩ := exists_with_decomposition L hL i Q (hQ.trans hfi.symm) hp ht
  exact ⟨D, hall⟩

/-- Every retained factor is nonzero and positive-arity by actual primality. -/
theorem factors_preprocessed {L : Language} (D : PrimeFactorization L) :
    Preprocessed D.factors := by
  rintro f ⟨⟨i, j⟩, rfl⟩
  exact ⟨D.positive i j, (D.prime i j).1⟩

/-- Retaining genuine prime factors preserves the preprocessing domain. -/
theorem retained_preprocessed {L : Language} (D : PrimeFactorization L)
    (hL : Preprocessed L.family) : Preprocessed (L.family ∪ D.factors) := by
  intro f hf
  rcases hf with hf | hf
  · exact hL f hf
  · exact D.factors_preprocessed f hf

end PrimeFactorization

/-- Paper 1 factor extraction now has a proved decomposition input for every
preprocessed language; its retained two-sided-family hypothesis is unchanged. -/
theorem factorClosure_exists (P : Paper1FactorClosureAccepted) (L : Language)
    (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family) :
    ∃ (D : PrimeFactorization L) (M : Language), M.family = L.family ∪ D.factors ∧
      Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M := by
  let D := PrimeFactorization.ofPreprocessed L hL
  obtain ⟨M, hM, hML, hLM⟩ := P.factorClosure_2_19 L hL htwo D
  exact ⟨D, M, hM, hML, hLM⟩

/-- Retained factor extraction with a prescribed member decomposition. This is
an actual finite exact-input augmentation, with enough invariants for iterating
factor extraction while keeping all original labels. -/
theorem factorClosure_with_member_decomposition (P : Paper1FactorClosureAccepted)
    (L : Language) (hL : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : (⟨n, f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (Q : TensorDecomposition AlgebraicComplex n) (hQ : Q.value = f)
    (hp : ∀ j, 0 < Q.arity j) (ht : ∀ j, TensorPrime (Q.factor j)) :
    ∃ M : Language, L.family ⊆ M.family ∧
      (∀ j, (⟨Q.arity j, Q.factor j⟩ : AnySignature AlgebraicComplex) ∈ M.family) ∧
      Preprocessed M.family ∧ ¬ CommonOneSided M.family ∧
      Problem.Reduces .nativeX M L ∧ Problem.Reduces .nativeX L M := by
  obtain ⟨D, hD⟩ := PrimeFactorization.exists_with_member_decomposition L hL f hf Q hQ hp ht
  obtain ⟨M, hM, hML, hLM⟩ := P.factorClosure_2_19 L hL htwo D
  have hsub : L.family ⊆ M.family := by rw [hM]; exact Set.subset_union_left
  refine ⟨M, hsub, ?_, ?_, ?_, hML, hLM⟩
  · intro j
    rw [hM]
    exact Or.inr (hD j)
  · rw [hM]
    exact D.retained_preprocessed hL
  · intro hs
    apply htwo
    rcases hs with hs | hs
    · exact Or.inl (fun g hg => hs g (hsub hg))
    · exact Or.inr (fun g hg => hs g (hsub hg))

end Paper2
