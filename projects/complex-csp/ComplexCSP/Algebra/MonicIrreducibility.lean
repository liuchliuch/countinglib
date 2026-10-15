import ComplexCSP.Recognition.MonicIrreducibilityBounds

/-!
# A finite, executable irreducibility test for monic integer polynomial codes

The runtime input is a finite integer coefficient vector with a declared degree.
The checker rejects a nonmonic leading coefficient. All arithmetic and equality
performed by the checker is integer/vector arithmetic; mathlib's non-executable
`Polynomial` ring is used only for the denotation and correctness proof.
-/

namespace ComplexCSP.MonicIrreducibility

open Polynomial
open scoped BigOperators

/-- Dense coefficients through the declared degree. -/
abbrev Code (n : ℕ) := Fin (n + 1) → ℤ

def coefficient {n : ℕ} (a : Code n) (i : ℕ) : ℤ :=
  if h : i < n + 1 then a ⟨i, h⟩ else 0

noncomputable def denote {n : ℕ} (a : Code n) : Polynomial ℤ :=
  ∑ i : Fin (n + 1), Polynomial.monomial i.val (a i)

@[simp] theorem denote_coeff {n : ℕ} (a : Code n) (i : ℕ) :
    (denote a).coeff i = coefficient a i := by
  classical
  simp only [denote, finset_sum_coeff, coeff_monomial]
  by_cases hi : i < n + 1
  · rw [coefficient, dif_pos hi]
    rw [Finset.sum_eq_single ⟨i, hi⟩]
    · simp
    · intro b _ hb
      simp only [ite_eq_right_iff]
      intro h
      exact False.elim (hb (Fin.ext h))
    · simp
  · simp only [coefficient, dif_neg hi]
    apply Finset.sum_eq_zero
    intro b _
    simp only [ite_eq_right_iff]
    intro h
    exact False.elim (hi (h ▸ b.isLt))

@[simp] theorem coefficient_at {n : ℕ} (a : Code n) (i : Fin (n+1)) :
    coefficient a i.val = a i := by simp [coefficient, i.isLt]

theorem denote_natDegree_le {n : ℕ} (a : Code n) : (denote a).natDegree ≤ n := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  simp [coefficient, show ¬i < n + 1 by omega]

theorem denote_monic {n : ℕ} (a : Code n) (ha : a ⟨n, by omega⟩ = 1) :
    (denote a).Monic := by
  apply Polynomial.monic_of_degree_le n
  · exact Polynomial.natDegree_le_iff_degree_le.mp (denote_natDegree_le a)
  · simpa [coefficient] using ha

theorem denote_natDegree {n : ℕ} (a : Code n) (ha : a ⟨n, by omega⟩ = 1) :
    (denote a).natDegree = n := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (denote_natDegree_le a)
  simp [coefficient, ha]

/-- Runtime Cauchy bound, read directly from the coefficient vector. -/
def rootBound {n : ℕ} (a : Code n) : ℕ :=
  (∑ i : Fin n, (a ⟨i.val, by omega⟩).natAbs) + 1

def coefficientBound {n : ℕ} (a : Code n) : ℕ := divisorBound n (rootBound a)

/-- A monic candidate of degree at most `n`, with bounded low coefficients. -/
abbrev Candidate (n C : ℕ) := Σ d : Fin (n+1), Fin d.val → Fin (2*C+1)

def candidateCoefficient {n C : ℕ} (a : Candidate n C) (i : ℕ) : ℤ :=
  if h : i < a.1.val then ((a.2 ⟨i,h⟩).val : ℤ) - C
  else if i = a.1.val then 1 else 0

def candidateCode {n C : ℕ} (a : Candidate n C) : Code n :=
  fun i ↦ candidateCoefficient a i.val

/-- Finite convolution, with no use of the polynomial ring at runtime. -/
def convolution {n : ℕ} (a b : Code n) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (k+1), coefficient a i * coefficient b (k-i)

/-- Exact product comparison; degrees of both factors are bounded by `n`. -/
def productMatches {n : ℕ} (a b p : Code n) : Bool :=
  decide (∀ k : Fin (2*n+1), convolution a b k.val = coefficient p k.val)

/-- Every search is explicitly finite. Degree zero and nonmonic input are
rejected before the factor search. -/
def irreducibleTest {n : ℕ} (p : Code n) : Bool :=
  if p ⟨n, by omega⟩ ≠ 1 ∨ n = 0 then false else
  let C := coefficientBound p
  !decide (∃ a b : Candidate n C,
    0 < a.1.val ∧ a.1.val ≤ n / 2 ∧ 0 < b.1.val ∧
      productMatches (candidateCode a) (candidateCode b) p = true)

theorem rootBound_eq {n : ℕ} (a : Code n) (ha : a ⟨n, by omega⟩ = 1) :
    rootBound a = EffectiveRoots.integerCauchyBound (denote a) := by
  rw [EffectiveRoots.integerCauchyBound, denote_natDegree a ha, Finset.sum_range]
  unfold rootBound
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  simp [coefficient, show i.val < n+1 by omega]

theorem convolution_eq {n : ℕ} (a b : Code n) (k : ℕ) :
    convolution a b k = ((denote a) * (denote b)).coeff k := by
  rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp [convolution]

@[simp] theorem productMatches_eq_true {n : ℕ} (a b p : Code n) :
    productMatches a b p = true ↔ denote a * denote b = denote p := by
  simp only [productMatches, decide_eq_true_eq]
  constructor
  · intro h
    apply Polynomial.ext
    intro k
    by_cases hk : k < 2*n+1
    · simpa only [convolution_eq, denote_coeff] using h ⟨k,hk⟩
    · have hab : (denote a * denote b).natDegree < k :=
        lt_of_le_of_lt (Polynomial.natDegree_mul_le.trans
          (Nat.add_le_add (denote_natDegree_le a) (denote_natDegree_le b))) (by omega)
      have hp : (denote p).natDegree < k := lt_of_le_of_lt (denote_natDegree_le p) (by omega)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hab,
        Polynomial.coeff_eq_zero_of_natDegree_lt hp]
  · intro h k
    rw [convolution_eq, h, denote_coeff]

theorem candidate_coefficient {n C : ℕ} (a : Candidate n C) (i : ℕ) :
    (denote (candidateCode a)).coeff i = candidateCoefficient a i := by
  rw [denote_coeff]
  by_cases hi : i < n+1
  · simp [coefficient, hi, candidateCode]
  · have hd : ¬i < a.1.val := by have := a.1.isLt; omega
    have he : i ≠ a.1.val := by have := a.1.isLt; omega
    simp [coefficient, hi, candidateCoefficient, hd, he]

theorem candidate_natDegree_le {n C : ℕ} (a : Candidate n C) :
    (denote (candidateCode a)).natDegree ≤ a.1.val := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [candidate_coefficient]
  simp [candidateCoefficient, show ¬ i < a.1.val by omega, show i ≠ a.1.val by omega]

theorem candidate_monic {n C : ℕ} (a : Candidate n C) :
    (denote (candidateCode a)).Monic := by
  apply Polynomial.monic_of_degree_le a.1.val
  · exact Polynomial.natDegree_le_iff_degree_le.mp (candidate_natDegree_le a)
  · simp [candidateCode, candidateCoefficient]

@[simp] theorem candidate_natDegree {n C : ℕ} (a : Candidate n C) :
    (denote (candidateCode a)).natDegree = a.1.val := by
  apply Polynomial.natDegree_eq_of_le_of_coeff_ne_zero (candidate_natDegree_le a)
  simp [candidateCode, candidateCoefficient]

/-- Every bounded monic polynomial is represented in the explicit finite search. -/
theorem exists_candidate {n C : ℕ} (q : Polynomial ℤ) (hq : q.Monic)
    (hd : q.natDegree ≤ n) (hc : ∀ i, (q.coeff i).natAbs ≤ C) :
    ∃ a : Candidate n C, denote (candidateCode a) = q := by
  let a : Candidate n C := ⟨⟨q.natDegree, by omega⟩,
    fun i ↦ ⟨(q.coeff i.val + (C : ℤ)).toNat, by
      have habs : |q.coeff i.val| ≤ (C : ℤ) := by
        have h : ((q.coeff i.val).natAbs : ℤ) ≤ C := by exact_mod_cast hc i.val
        simpa only [Int.natCast_natAbs] using h
      have hb := abs_le.mp habs
      apply (Int.toNat_lt (by omega)).mpr
      omega⟩⟩
  refine ⟨a, ?_⟩
  apply Polynomial.ext
  intro i
  rw [candidate_coefficient]
  change (if h : i < q.natDegree then
    (((q.coeff i + (C : ℤ)).toNat : ℕ) : ℤ) - C
    else if i = q.natDegree then 1 else 0) = q.coeff i
  by_cases hi : i < q.natDegree
  · rw [dif_pos hi, Int.toNat_of_nonneg]
    · ring
    · have habs : |q.coeff i| ≤ (C : ℤ) := by
        have h : ((q.coeff i).natAbs : ℤ) ≤ C := by exact_mod_cast hc i
        simpa only [Int.natCast_natAbs] using h
      have := (abs_le.mp habs).1
      omega
  · rw [dif_neg hi]
    by_cases he : i = q.natDegree
    · subst i; simp [hq.coeff_natDegree]
    · rw [if_neg he, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

theorem candidate_exists_for_divisor {n : ℕ} (p : Code n)
    (hp : p ⟨n, by omega⟩ = 1) (q : Polynomial ℤ)
    (hq : q.Monic) (hqp : q ∣ denote p) :
    ∃ a : Candidate n (coefficientBound p), denote (candidateCode a) = q := by
  apply exists_candidate q hq
  · simpa [denote_natDegree p hp] using
      Polynomial.natDegree_le_of_dvd hqp (denote_monic p hp).ne_zero
  · intro i
    have h := monic_divisor_coeff_bound (denote p) q (denote_monic p hp) hq hqp i
    simpa [coefficientBound, denote_natDegree p hp, ← rootBound_eq p hp] using h

/-- The finite integer search decides irreducibility over the integers. -/
theorem irreducibleTest_correct_int {n : ℕ} (p : Code n)
    (hp : p ⟨n, by omega⟩ = 1) :
    irreducibleTest p = true ↔ Irreducible (denote p) := by
  have hmon : (denote p).Monic := denote_monic p hp
  have hdegree := denote_natDegree p hp
  by_cases hn : n = 0
  · have heq : denote p = 1 := Polynomial.eq_one_of_monic_natDegree_zero hmon (hdegree.trans hn)
    simp [irreducibleTest, hn, heq]
  have hne : denote p ≠ 1 := by
    intro h
    have : (denote p).natDegree = 0 := by rw [h]; simp
    omega
  simp only [irreducibleTest, hp, ne_eq, not_true_eq_false, false_or, hn, ↓reduceIte]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not]
  constructor
  · intro htest
    apply (hmon.irreducible_iff_lt_natDegree_lt hne).mpr
    intro q hq hd hdvd
    obtain ⟨r, hr⟩ := hdvd
    have hrmon : r.Monic := hq.of_mul_monic_left (hr ▸ hmon)
    have hsum : q.natDegree + r.natDegree = n := by
      rw [← hq.natDegree_mul hrmon, ← hr, hdegree]
    have hqd : 0 < q.natDegree ∧ q.natDegree ≤ n/2 := by
      simpa [Finset.mem_Ioc, hdegree] using hd
    have hrd : 0 < r.natDegree := by omega
    obtain ⟨a, ha⟩ := candidate_exists_for_divisor p hp q hq ⟨r,hr⟩
    obtain ⟨b, hb⟩ := candidate_exists_for_divisor p hp r hrmon
      ⟨q, by rw [mul_comm]; exact hr⟩
    have had : a.1.val = q.natDegree := by rw [← candidate_natDegree a, ha]
    have hbd : b.1.val = r.natDegree := by rw [← candidate_natDegree b, hb]
    apply htest
    refine ⟨a,b, by omega, by omega, by omega, ?_⟩
    apply (productMatches_eq_true _ _ _).mpr
    rw [ha,hb]
    exact hr.symm
  · intro hirr
    rintro ⟨a,b,ha,_,hb,hab⟩
    have hprod := (productMatches_eq_true _ _ _).mp hab
    have ha' : (denote (candidateCode a)).natDegree = 0 ∨
        (denote (candidateCode b)).natDegree = 0 :=
      (hmon.irreducible_iff_natDegree.mp hirr).2 _ _
        (candidate_monic a) (candidate_monic b) hprod
    simp only [candidate_natDegree] at ha'
    omega

/-- Gauss's lemma gives the intended rational irreducibility decision. -/
theorem irreducibleTest_correct_rat {n : ℕ} (p : Code n)
    (hp : p ⟨n, by omega⟩ = 1) :
    irreducibleTest p = true ↔
      Irreducible ((denote p).map (Int.castRingHom ℚ)) := by
  rw [irreducibleTest_correct_int p hp]
  exact (denote_monic p hp).irreducible_iff_irreducible_map_fraction_map

/-- The implicit-leading-one input convention used by the exact-field codec. -/
def fromTail {n : ℕ} (a : Fin n → ℤ) : Code n :=
  fun i ↦ if h : i.val < n then a ⟨i.val,h⟩ else 1

def irreducibleMonicTail {n : ℕ} (a : Fin n → ℤ) : Bool :=
  irreducibleTest (fromTail a)

def irreducibleMonicList (a : List ℤ) : Bool :=
  irreducibleMonicTail (fun i : Fin a.length ↦ a.get i)

@[simp] theorem fromTail_leading {n : ℕ} (a : Fin n → ℤ) :
    fromTail a ⟨n, by omega⟩ = 1 := by simp [fromTail]

theorem irreducibleMonicTail_correct {n : ℕ} (a : Fin n → ℤ) :
    irreducibleMonicTail a = true ↔
      Irreducible ((denote (fromTail a)).map (Int.castRingHom ℚ)) :=
  irreducibleTest_correct_rat _ (fromTail_leading a)

theorem irreducibleMonicList_correct (a : List ℤ) :
    irreducibleMonicList a = true ↔
      Irreducible ((denote (fromTail (fun i : Fin a.length ↦ a.get i))).map
        (Int.castRingHom ℚ)) :=
  irreducibleMonicTail_correct _

/-- Denotation agrees with any semantic monic polynomial carrying these low
coefficients and the declared degree. -/
theorem denote_fromTail_eq {n : ℕ} (a : Fin n → ℤ) (p : Polynomial ℤ)
    (hp : p.Monic) (hd : p.natDegree = n)
    (hc : ∀ i : Fin n, p.coeff i.val = a i) : denote (fromTail a) = p := by
  apply Polynomial.ext
  intro i
  rw [denote_coeff]
  by_cases hi : i < n
  · simp only [coefficient, show i < n+1 by omega, ↓reduceDIte, fromTail, hi]
    exact (hc ⟨i,hi⟩).symm
  · by_cases he : i = n
    · subst i
      simpa [coefficient, fromTail, ← hd] using hp.coeff_natDegree.symm
    · have hn : n < i := by omega
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hd ▸ hn)]
      simp [coefficient, show ¬i < n+1 by omega]

/-- Uniform encoded-input correctness without requiring our particular
semantic polynomial constructor at the call site. -/
theorem irreducibleMonicTail_correct_of_coeff {n : ℕ} (a : Fin n → ℤ)
    (p : Polynomial ℤ) (hp : p.Monic) (hd : p.natDegree = n)
    (hc : ∀ i : Fin n, p.coeff i.val = a i) :
    irreducibleMonicTail a = true ↔ Irreducible (p.map (Int.castRingHom ℚ)) := by
  rw [irreducibleMonicTail_correct, denote_fromTail_eq a p hp hd hc]

theorem irreducibleTest_nonmonic {n : ℕ} (p : Code n)
    (hp : p ⟨n, by omega⟩ ≠ 1) : irreducibleTest p = false := by
  simp [irreducibleTest, hp]

theorem irreducibleMonicTail_degree_zero (a : Fin 0 → ℤ) :
    irreducibleMonicTail a = false := by simp [irreducibleMonicTail, irreducibleTest]

theorem irreducibleMonicTail_degree_one (a : Fin 1 → ℤ) :
    irreducibleMonicTail a = true := by
  simp only [irreducibleMonicTail, irreducibleTest, fromTail_leading, ne_eq,
    not_true_eq_false, Nat.one_ne_zero, or_self, ↓reduceIte, Bool.not_eq_true',
    decide_eq_false_iff_not]
  rintro ⟨c,d,hc,hc',_,_⟩
  omega

/-- Total raw-vector specification, including the explicit monicity guard. -/
theorem irreducibleTest_correct_guarded {n : ℕ} (p : Code n) :
    irreducibleTest p = true ↔ p ⟨n, by omega⟩ = 1 ∧
      Irreducible ((denote p).map (Int.castRingHom ℚ)) := by
  by_cases hp : p ⟨n, by omega⟩ = 1
  · simp only [hp, true_and]
    exact irreducibleTest_correct_rat p hp
  · simp [irreducibleTest_nonmonic p hp, hp]

/-- Every semantic monic integer polynomial has a finite list code. This is an
existence proof for termination arguments, not a runtime coefficient oracle. -/
theorem exists_monicList (p : Polynomial ℤ) (hp : p.Monic) :
    ∃ a : List ℤ, a.length = p.natDegree ∧
      denote (fromTail (fun i : Fin a.length ↦ a.get i)) = p := by
  let a := List.ofFn (fun i : Fin p.natDegree ↦ p.coeff i.val)
  have hlen : a.length = p.natDegree := List.length_ofFn
  refine ⟨a, hlen, ?_⟩
  apply denote_fromTail_eq _ p hp hlen.symm
  intro i
  simp [a]

end ComplexCSP.MonicIrreducibility
