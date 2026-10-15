import ComplexCSP.Algebra.UniformCyclotomicExtensionSearch
import ComplexCSP.Algebra.EncodedNumberFieldValidation

/-!
# A terminating cyclotomic search from validated raw integer input

The runtime input is a monic integer tail and a positive root order. The old
field model is derived from the actual finite irreducibility checker, solely
inside the existence proof used to justify the search.
-/
namespace ComplexCSP.AlgebraicEncoding
open Polynomial EncodedNumberField
open scoped BigOperators

variable {n : ℕ}

/-- The model's reduction relation implies the literal integer polynomial vanishes. -/
theorem model_integer_polynomial_root (a : Fin n → ℤ)
    (M : Element.Model n (EffectiveRoots.coefficientRelation a)) :
    aeval M.generator (MonicIrreducibility.denote (MonicIrreducibility.fromTail a)) = 0 := by
  let p := MonicIrreducibility.denote (MonicIrreducibility.fromTail a)
  have hp : p.Monic := MonicIrreducibility.denote_monic _
    (MonicIrreducibility.fromTail_leading a)
  have hd : p.natDegree = n := MonicIrreducibility.denote_natDegree _
    (MonicIrreducibility.fromTail_leading a)
  have htop : p.coeff n = 1 := by rw [← hd, hp.coeff_natDegree]
  have hcoeff (i : Fin n) : p.coeff i.val = a i := by
    simp [p, MonicIrreducibility.coefficient, MonicIrreducibility.fromTail,
      i.isLt, show i.val < n + 1 by omega]
  change aeval M.generator p = 0
  rw [aeval_eq_sum_range, hd, Finset.sum_range_succ, htop, one_smul, Finset.sum_range]
  simp only [hcoeff, zsmul_eq_mul]
  rw [M.relation]
  simp [interpret, EffectiveRoots.coefficientRelation, Finset.sum_neg_distrib]

theorem transportedPowerBasis_dim {K : Type} [Field K]
    {A B : Algebra ℚ K} (h : A = B) (pb : @PowerBasis ℚ K _ _ A) :
    @PowerBasis.dim ℚ K _ _ B (h ▸ pb) = @PowerBasis.dim ℚ K _ _ A pb := by
  cases h
  rfl

theorem transportedPowerBasis_gen {K : Type} [Field K]
    {A B : Algebra ℚ K} (h : A = B) (pb : @PowerBasis ℚ K _ _ A) :
    @PowerBasis.gen ℚ K _ _ B (h ▸ pb) = @PowerBasis.gen ℚ K _ _ A pb := by
  cases h
  rfl

attribute [-instance] Element.Model.algebra in
/-- A model's rational action agrees with the canonical characteristic-zero action. -/
noncomputable def modelCanonicalPowerBasis {c : CoeffVector n}
    (M : Element.Model n c) [CharZero M.K] : PowerBasis ℚ M.K := by
  have h : M.algebra = DivisionRing.toRatAlgebra := Subsingleton.elim _ _
  let pb : PowerBasis ℚ M.K := h ▸ M.powerBasis
  have hd : pb.dim = n := transportedPowerBasis_dim h M.powerBasis
  have hg : pb.gen = M.generator := transportedPowerBasis_gen h M.powerBasis
  refine ⟨M.generator, n, pb.basis.reindex (finCongr hd), ?_⟩
  intro i
  rw [Module.Basis.reindex_apply, pb.basis_eq_pow, hg]
  rfl

attribute [-instance] Element.Model.algebra in
@[simp] theorem modelCanonicalPowerBasis_dim {c : CoeffVector n}
    (M : Element.Model n c) [CharZero M.K] : (modelCanonicalPowerBasis M).dim = n := rfl

attribute [-instance] Element.Model.algebra in
@[simp] theorem modelCanonicalPowerBasis_gen {c : CoeffVector n}
    (M : Element.Model n c) [CharZero M.K] : (modelCanonicalPowerBasis M).gen = M.generator := rfl

attribute [-instance] Element.Model.algebra in
/-- Any genuine rational power-basis model is a number field. -/
def modelNumberField {c : CoeffVector n} (M : Element.Model n c) : NumberField M.K := by
  letI : Algebra ℚ M.K := M.algebra
  letI : CharZero M.K := charZero_of_injective_algebraMap (algebraMap ℚ M.K).injective
  letI : Algebra ℚ M.K := DivisionRing.toRatAlgebra
  exact { to_charZero := inferInstance, to_finiteDimensional := (modelCanonicalPowerBasis M).finite }

attribute [-instance] Element.Model.algebra in
/-- The validated raw code acquires the integral presentation required by the
existence argument, with basis dimension definitionally equal to the input length. -/
noncomputable def validatedIntegralPresentation (a : Fin n → ℤ)
    (ha : MonicIrreducibility.irreducibleMonicTail a = true)
    (M : Element.Model n (EffectiveRoots.coefficientRelation a)) :
    letI := modelNumberField M
    IntegralPrimitivePresentation M.K := by
  letI := modelNumberField M
  let p := MonicIrreducibility.denote (MonicIrreducibility.fromTail a)
  have hp : p.Monic := MonicIrreducibility.denote_monic _
    (MonicIrreducibility.fromTail_leading a)
  have hi : Irreducible (p.map (Int.castRingHom ℚ)) :=
    (MonicIrreducibility.irreducibleMonicTail_correct a).mp ha
  have hr : aeval M.generator p = 0 := model_integer_polynomial_root a M
  refine ⟨modelCanonicalPowerBasis M, ?_, p, hp, ?_, ?_⟩
  · rw [modelCanonicalPowerBasis_gen]
    exact ⟨p, hp, hr⟩
  · exact (hp.irreducible_iff_irreducible_map_fraction_map (K := ℚ)).mpr hi
  · rw [modelCanonicalPowerBasis_gen]
    apply minpoly.eq_of_irreducible_of_monic hi _ (hp.map _)
    change aeval M.generator (p.map (algebraMap ℤ ℚ)) = 0
    rw [aeval_map_algebraMap]
    exact hr

attribute [-instance] Element.Model.algebra in
/-- Existence of an accepted code follows from finite validation alone. -/
theorem exists_accepted_code_of_valid_tail (a : Fin n → ℤ)
    (ha : MonicIrreducibility.irreducibleMonicTail a = true) (δ : ℕ) (hδ : 0 < δ) :
    ∃ code, (cyclotomicCandidateFromCode code).test a δ = true := by
  obtain ⟨M⟩ := Element.valid_of_irreducibleMonicTail a ha
  letI := modelNumberField M
  let P := validatedIntegralPresentation a ha M
  apply exists_accepted_cyclotomic_code P a _ δ hδ
  intro i
  have hi : i.val < n := i.isLt
  change (MonicIrreducibility.denote (MonicIrreducibility.fromTail a)).coeff i.val = a i
  simp [MonicIrreducibility.coefficient, MonicIrreducibility.fromTail,
    hi, show i.val < n + 1 by omega]
  rfl

/-- Two cheap candidates retain the original field for roots 1 and -1; every
other finite candidate remains in the complete enumeration. -/
def cyclotomicCandidateAt (a : Fin n → ℤ) : ℕ → CyclotomicCandidate
  | 0 => ⟨n, a, generatorCoordinates (EffectiveRoots.coefficientRelation a), one n, 1, 0⟩
  | 1 => ⟨n, a, generatorCoordinates (EffectiveRoots.coefficientRelation a), neg (one n), 1, 0⟩
  | k + 2 => cyclotomicCandidateFromCode k

 theorem exists_accepted_candidateAt (a : Fin n → ℤ)
    (ha : MonicIrreducibility.irreducibleMonicTail a = true) (δ : ℕ) (hδ : 0 < δ) :
    ∃ code, (cyclotomicCandidateAt a code).test a δ = true := by
  obtain ⟨code, hc⟩ := exists_accepted_code_of_valid_tail a ha δ hδ
  exact ⟨code + 2, hc⟩

/-- An actual terminating search over integer/rational candidate records. -/
def findCyclotomicCode (a : Fin n → ℤ)
    (ha : MonicIrreducibility.irreducibleMonicTail a = true) (δ : ℕ) (hδ : 0 < δ) : ℕ :=
  Nat.find (exists_accepted_candidateAt a ha δ hδ)

 theorem findCyclotomicCode_spec (a : Fin n → ℤ)
    (ha : MonicIrreducibility.irreducibleMonicTail a = true) (δ : ℕ) (hδ : 0 < δ) :
    (cyclotomicCandidateAt a (findCyclotomicCode a ha δ hδ)).test a δ = true :=
  Nat.find_spec (exists_accepted_candidateAt a ha δ hδ)

/-- The searched finite presentation, with no supplied extension model or oracle. -/
def findCyclotomicCandidate (a : Fin n → ℤ)
    (ha : MonicIrreducibility.irreducibleMonicTail a = true) (δ : ℕ) (hδ : 0 < δ) :
    CyclotomicCandidate := cyclotomicCandidateAt a (findCyclotomicCode a ha δ hδ)

 theorem findCyclotomicCandidate_spec (a : Fin n → ℤ)
    (ha : MonicIrreducibility.irreducibleMonicTail a = true) (δ : ℕ) (hδ : 0 < δ) :
    (findCyclotomicCandidate a ha δ hδ).test a δ = true :=
  findCyclotomicCode_spec a ha δ hδ

/-- Literal raw-input entry point; invalid polynomials and order zero are rejected. -/
def checkedCyclotomicExtension (a : Fin n → ℤ) (δ : ℕ) : Option CyclotomicCandidate :=
  if h : MonicIrreducibility.irreducibleMonicTail a = true ∧ 0 < δ then
    some (findCyclotomicCandidate a h.1 δ h.2)
  else none

 theorem checkedCyclotomicExtension_success (a : Fin n → ℤ)
    (ha : MonicIrreducibility.irreducibleMonicTail a = true) (δ : ℕ) (hδ : 0 < δ) :
    ∃ C, checkedCyclotomicExtension a δ = some C ∧ C.test a δ = true := by
  refine ⟨findCyclotomicCandidate a ha δ hδ, ?_, findCyclotomicCandidate_spec a ha δ hδ⟩
  simp [checkedCyclotomicExtension, ha, hδ]

 theorem checkedCyclotomicExtension_rejects (a : Fin n → ℤ) (δ : ℕ)
    (h : MonicIrreducibility.irreducibleMonicTail a = false ∨ δ = 0) :
    checkedCyclotomicExtension a δ = none := by
  rcases h with h | h <;> simp [checkedCyclotomicExtension, h]

/-- Every successful raw call certifies its validation and exact finite equations. -/
theorem checkedCyclotomicExtension_sound (a : Fin n → ℤ) (δ : ℕ)
    (C : CyclotomicCandidate) (h : checkedCyclotomicExtension a δ = some C) :
    MonicIrreducibility.irreducibleMonicTail a = true ∧ 0 < δ ∧ C.test a δ = true := by
  unfold checkedCyclotomicExtension at h
  split_ifs at h with hv
  · have he := Option.some.inj h
    subst C
    exact ⟨hv.1, hv.2, findCyclotomicCandidate_spec a hv.1 δ hv.2⟩

/-- A list-input wrapper, without native polynomial construction. -/
def checkedCyclotomicList (a : List ℤ) (δ : ℕ) : Option CyclotomicCandidate :=
  checkedCyclotomicExtension a.get δ

/-- Successful finite tests have actual quotient-field semantics. -/
theorem candidate_test_sound {r : ℕ} (old : Fin r → ℤ) (δ : ℕ) (hδ : 0 < δ)
    (C : CyclotomicCandidate) (hC : C.test old δ = true) :
    ∃ M : Element.Model C.dimension C.relation,
      0 < C.d ∧
      aeval (interpret M.generator C.oldGenerator)
        (MonicIrreducibility.denote (MonicIrreducibility.fromTail old)) = 0 ∧
      IsPrimitiveRoot (interpret M.generator C.root) δ ∧
      M.generator = (C.d : M.K) * interpret M.generator C.oldGenerator +
        (C.m : M.K) * interpret M.generator C.root := by
  have ht := of_decide_eq_true hC
  obtain ⟨M⟩ := Element.valid_of_irreducibleMonicTail C.tail ht.2.2.1
  have hc := (candidateTest_correct_in_model M.powerBasis C.tail C.oldGenerator C.root
    C.d C.m old δ hδ M.relation).mp hC
  exact ⟨M, hc.1, hc.2.2⟩

end ComplexCSP.AlgebraicEncoding
