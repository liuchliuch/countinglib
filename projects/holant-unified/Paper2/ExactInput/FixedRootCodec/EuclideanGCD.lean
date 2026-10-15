import Paper2.ExactInput.FixedRootCodec.SturmMachines

/-! The Euclidean algorithm on runtime rational coefficient vectors. The
number of stages is fixed by the vector capacity. Its terminal polynomial
is a genuine greatest common divisor, with its actual scalar retained. -/
namespace Paper2.ExactInput.FixedRootCodec.VariablePolynomial
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines BellMachines Polynomial
noncomputable section

theorem polynomial_eq_zero_iff {n : ℕ} (v : Fin n → ℚ) :
    polynomial v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext i
    have hc := congrArg (fun p : ℚ[X] => p.coeff i.val) h
    simpa [coefficient_eq,i.isLt] using hc
  · rintro rfl
    simp [polynomial]

theorem polynomial_natDegree_lt {n : ℕ} (v : Fin n → ℚ) (hn : 0 < n) :
    (polynomial v).natDegree < n := by
  by_cases hp : polynomial v = 0
  · simpa [hp] using hn
  apply (natDegree_lt_iff_degree_lt hp).mpr
  apply (degree_lt_iff_coeff_zero _ _).mpr
  intro k hk
  rw [coefficient_eq]
  have h : ¬ k < n := by omega
  simp [h]

def gcdStep {n : ℕ} (p : Pair n) : Pair n :=
  if p.2 = 0 then p else (p.2,-remainder p)

def gcdStepComputes (n : ℕ) :
    Computes (pairVectorEncoding n) (pairVectorEncoding n) (gcdStep (n := n)) :=
  congrComputes (ifComputes
    ((Wiring.secondComputes _ _).andThen (FixedRootCodec.zeroComputes (vectorEncoding n)))
    (identityComputes _)
    (pairComputes (Wiring.secondComputes _ _)
      ((remainderComputes n).andThen (negateComputes n))))
    (fun p => by simp only [gcdStep,Function.comp_apply,decide_eq_true_eq,id_eq])

def gcdStage {n : ℕ} (p : Pair n) : ℕ → Pair n
  | 0 => p
  | k+1 => gcdStep (gcdStage p k)

def gcdStageComputes (n : ℕ) : (k : ℕ) →
    Computes (pairVectorEncoding n) (pairVectorEncoding n) (fun p => gcdStage p k)
  | 0 => identityComputes _
  | k+1 => congrComputes ((gcdStageComputes n k).andThen (gcdStepComputes n))
      (fun _ => rfl)

def degreeWeight (p : ℚ[X]) : ℕ := if p = 0 then 0 else p.natDegree+1

@[simp] theorem degreeWeight_zero : degreeWeight 0 = 0 := by simp [degreeWeight]

theorem degreeWeight_pos {p : ℚ[X]} (hp : p ≠ 0) : 0 < degreeWeight p := by
  simp [degreeWeight,hp]

theorem degreeWeight_vector_le {n : ℕ} (v : Fin n → ℚ) :
    degreeWeight (polynomial v) ≤ n := by
  by_cases hp : polynomial v = 0
  · simp [degreeWeight,hp]
  · have hn : 0 < n := by
      by_contra h
      have hn : n=0 := by omega
      subst n
      simp [polynomial] at hp
    simp only [degreeWeight,hp,ite_false]
    exact polynomial_natDegree_lt v hn

theorem gcdStep_weight {n : ℕ} (p : Pair n) (hq : p.2 ≠ 0) :
    degreeWeight (polynomial (gcdStep p).2) < degreeWeight (polynomial p.2) := by
  have hq' : polynomial p.2 ≠ 0 := fun hz => hq ((polynomial_eq_zero_iff _).mp hz)
  simp only [gcdStep,hq,ite_false,negate_polynomial,remainder_polynomial]
  by_cases hr : polynomial p.1 % polynomial p.2 = 0
  · simp only [hr,neg_zero,degreeWeight_zero]
    exact degreeWeight_pos hq'
  · have hr' : -(polynomial p.1 % polynomial p.2) ≠ 0 := neg_ne_zero.mpr hr
    simp only [degreeWeight,hr',hq',ite_false,natDegree_neg]
    exact Nat.add_lt_add_right
      (natDegree_lt_natDegree hr (degree_mod_lt _ hq')) 1

theorem gcdStage_weight {n : ℕ} (p : Pair n) (k : ℕ)
    (hq : (gcdStage p k).2 ≠ 0) :
    degreeWeight (polynomial (gcdStage p k).2)+k ≤ degreeWeight (polynomial p.2) := by
  induction k with
  | zero => simp [gcdStage]
  | succ k ih =>
    have hk : (gcdStage p k).2 ≠ 0 := by
      intro hz
      have hz' : (gcdStage p (k+1)).2=0 := by simp [gcdStage,gcdStep,hz]
      exact hq hz'
    have hs := gcdStep_weight (gcdStage p k) hk
    have hi := ih hk
    change degreeWeight (polynomial (gcdStep (gcdStage p k)).2)+(k+1) ≤ _
    omega

theorem gcdStage_terminal {n : ℕ} (p : Pair n) : (gcdStage p n).2 = 0 := by
  by_contra h
  have hw := gcdStage_weight p n h
  have hb := degreeWeight_vector_le p.2
  have hp : polynomial (gcdStage p n).2 ≠ 0 :=
    fun hz => h ((polynomial_eq_zero_iff _).mp hz)
  have hh := degreeWeight_pos hp
  omega

theorem gcdStep_common_divisor {n : ℕ} (p : Pair n) (a : ℚ[X]) :
    (a ∣ polynomial (gcdStep p).1 ∧ a ∣ polynomial (gcdStep p).2) ↔
      (a ∣ polynomial p.1 ∧ a ∣ polynomial p.2) := by
  by_cases hq : p.2 = 0
  · simp [gcdStep,hq]
  · simp only [gcdStep,hq,ite_false,negate_polynomial,remainder_polynomial,dvd_neg]
    constructor
    · rintro ⟨h1,h2⟩
      exact ⟨(EuclideanDomain.dvd_mod_iff h1).mp h2,h1⟩
    · rintro ⟨h1,h2⟩
      exact ⟨h2,(EuclideanDomain.dvd_mod_iff h2).mpr h1⟩

theorem gcdStage_common_divisor {n : ℕ} (p : Pair n) (k : ℕ) (a : ℚ[X]) :
    (a ∣ polynomial (gcdStage p k).1 ∧ a ∣ polynomial (gcdStage p k).2) ↔
      (a ∣ polynomial p.1 ∧ a ∣ polynomial p.2) := by
  induction k with
  | zero => rfl
  | succ k ih => exact (gcdStep_common_divisor (gcdStage p k) a).trans ih

theorem gcdStage_nonzero {n : ℕ} (p : Pair n) (k : ℕ)
    (hp : p.1 ≠ 0 ∨ p.2 ≠ 0) :
    (gcdStage p k).1 ≠ 0 ∨ (gcdStage p k).2 ≠ 0 := by
  induction k with
  | zero => exact hp
  | succ k ih =>
    by_cases hq : (gcdStage p k).2=0
    · simpa [gcdStage,gcdStep,hq] using ih
    · simp only [gcdStage,gcdStep,hq,ite_false]
      exact Or.inl hq

def gcdVector {n : ℕ} (p : Pair n) : Fin n → ℚ := (gcdStage p n).1

def gcdComputes (n : ℕ) :
    Computes (pairVectorEncoding n) (vectorEncoding n) (gcdVector (n := n)) :=
  congrComputes ((gcdStageComputes n n).andThen (Wiring.firstComputes _ _)) (fun _ => rfl)

theorem gcdVector_divisors {n : ℕ} (p : Pair n) (a : ℚ[X]) :
    a ∣ polynomial (gcdVector p) ↔ a ∣ polynomial p.1 ∧ a ∣ polynomial p.2 := by
  have h := gcdStage_common_divisor p n a
  rw [gcdStage_terminal p] at h
  simpa [gcdVector,polynomial] using h

theorem gcdVector_ne_zero {n : ℕ} (p : Pair n) (hp : p.1 ≠ 0 ∨ p.2 ≠ 0) :
    gcdVector p ≠ 0 := by
  have h := gcdStage_nonzero p n hp
  rw [gcdStage_terminal p] at h
  simpa [gcdVector] using h

def derivativeGCDComputes (n : ℕ) :
    Computes (vectorEncoding n) (vectorEncoding n)
      (fun v : Fin n → ℚ => gcdVector (v,derivative v)) :=
  congrComputes ((initialComputes n).andThen (gcdComputes n)) (fun _ => rfl)

theorem derivativeGCD_divisors {n : ℕ} (v : Fin n → ℚ) (a : ℚ[X]) :
    a ∣ polynomial (gcdVector (v,derivative v)) ↔
      a ∣ polynomial v ∧ a ∣ (polynomial v).derivative := by
  simpa [derivative_polynomial] using gcdVector_divisors (v,derivative v) a

end
end Paper2.ExactInput.FixedRootCodec.VariablePolynomial
