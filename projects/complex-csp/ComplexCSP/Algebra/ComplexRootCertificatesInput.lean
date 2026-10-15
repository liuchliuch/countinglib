import ComplexCSP.Algebra.ComplexRootCertificatesComplete
import Mathlib.Data.List.GetD

/-! # Literal rational/integer list ingress and joint certificate checking -/

namespace ComplexCSP.ComplexRootCertificates

open Polynomial GaussianRational
open scoped BigOperators

/-- Literal coefficient lists, in ascending degree order; two trailing zero
slots provide the constant/linear Taylor coordinates even for an empty list. -/
def ofRatList (a : List ℚ) : Code a.length :=
  fun i ↦ ⟨a.getD i.val 0, 0⟩

def ofIntList (a : List ℤ) : Code a.length :=
  fun i ↦ ⟨(a.getD i.val 0 : ℚ), 0⟩

def rootCertificateRat (a : List ℚ) (c : GaussianRational) (r : ℚ) : Bool :=
  rootCertificate (ofRatList a) c r

def rootCertificateInt (a : List ℤ) (c : GaussianRational) (r : ℚ) : Bool :=
  rootCertificate (ofIntList a) c r

/-- A simultaneously checkable finite family of image requirements. -/
def jointCertificate {n : ℕ} (a : Code n) {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (q : ∀ i, Code (m i)) (box : ι → Rectangle)
    (c : GaussianRational) (r : ℚ) : Bool :=
  rootCertificate a c r && decide (∀ i, imageCertificate (q i) c r (box i) = true)

@[simp] theorem jointCertificate_eq_true {n : ℕ} (a : Code n) {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (q : ∀ i, Code (m i)) (box : ι → Rectangle)
    (c : GaussianRational) (r : ℚ) : jointCertificate a m q box c r = true ↔
      rootCertificate a c r = true ∧ ∀ i, imageCertificate (q i) c r (box i) = true := by
  simp [jointCertificate]

theorem jointCertificate_sound {n : ℕ} (a : Code n) {ι : Type*} [Fintype ι]
    (m : ι → ℕ) (q : ∀ i, Code (m i)) (box : ι → Rectangle)
    (c : GaussianRational) (r : ℚ) (h : jointCertificate a m q box c r = true) :
    ∃! z : ℂ, ‖z-toComplex c‖ ≤ (r:ℝ) ∧ (denote a).eval z = 0 ∧
      ∀ i, (box i).Contains ((denote (q i)).eval z) := by
  obtain ⟨ha,hq⟩ := (jointCertificate_eq_true a m q box c r).mp h
  obtain ⟨z,hz,hunique⟩ := rootCertificate_sound a c r ha
  refine ⟨z, ⟨hz.1,hz.2,fun i ↦ imageCertificate_sound _ _ _ _ (hq i) z hz.1⟩, ?_⟩
  intro w hw
  exact hunique w ⟨hw.1,hw.2.1⟩

theorem jointCertificate_complete {n : ℕ} (a : Code n) (α : ℂ)
    (hroot : (denote a).eval α = 0) (hsimple : (denote a).derivative.eval α ≠ 0)
    {ι : Type*} [Fintype ι] (m : ι → ℕ) (q : ∀ i, Code (m i))
    (box : ι → Rectangle) (hbox : ∀ i, (box i).Contains ((denote (q i)).eval α))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ (c : GaussianRational) (r : ℚ), 0 < r ∧ (r:ℝ) < ε ∧
      ‖toComplex c-α‖ < (r:ℝ) ∧ jointCertificate a m q box c r = true := by
  obtain ⟨c,r,hr,hsmall,hclose,hcert,himages⟩ :=
    exists_certificates_of_simple_root a α hroot hsimple m q box hbox ε hε
  exact ⟨c,r,hr,hsmall,hclose,(jointCertificate_eq_true a m q box c r).mpr ⟨hcert,himages⟩⟩

/-- The semantic denotation's coefficient is exactly the supplied finite data. -/
theorem denote_coeff {n : ℕ} (a : Code n) (k : ℕ) :
    (denote a).coeff k = if h : k < n+2 then toComplex (a ⟨k,h⟩) else 0 := by
  classical
  simp only [denote, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial]
  by_cases hk : k < n+2
  · rw [dif_pos hk, Finset.sum_eq_single ⟨k,hk⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      exact fun h ↦ hb (Fin.ext h)
    · simp
  · rw [dif_neg hk]
    apply Finset.sum_eq_zero
    intro i _
    rw [if_neg]
    exact fun h ↦ hk (h ▸ i.isLt)

@[simp] theorem denote_ofRatList_coeff (a : List ℚ) (k : ℕ) :
    (denote (ofRatList a)).coeff k = (a.getD k 0 : ℂ) := by
  rw [denote_coeff]
  by_cases hk : k < a.length+2
  · rw [dif_pos hk]
    apply Complex.ext <;> simp [ofRatList]
  · rw [dif_neg hk, List.getD_eq_default a 0 (by omega)]
    simp

@[simp] theorem denote_ofIntList_coeff (a : List ℤ) (k : ℕ) :
    (denote (ofIntList a)).coeff k = (a.getD k 0 : ℂ) := by
  rw [denote_coeff]
  by_cases hk : k < a.length+2
  · rw [dif_pos hk]
    apply Complex.ext <;> simp [ofIntList]
  · rw [dif_neg hk, List.getD_eq_default a 0 (by omega)]
    simp

/-- Correctness can be stated against any supplied rational polynomial, without
constructing a native polynomial at runtime. -/
theorem denote_ofRatList_eq (a : List ℚ) (p : Polynomial ℚ)
    (hcoeff : ∀ k, p.coeff k = a.getD k 0) :
    denote (ofRatList a) = p.map (Rat.castHom ℂ) := by
  apply Polynomial.ext
  intro k
  simp [hcoeff]

theorem denote_ofIntList_eq (a : List ℤ) (p : Polynomial ℤ)
    (hcoeff : ∀ k, p.coeff k = a.getD k 0) :
    denote (ofIntList a) = p.map (Int.castRingHom ℂ) := by
  apply Polynomial.ext
  intro k
  simp [hcoeff]

/-- Every semantic rational polynomial has a literal finite coefficient list. -/
theorem exists_ratList (p : Polynomial ℚ) :
    ∃ a : List ℚ, denote (ofRatList a) = p.map (Rat.castHom ℂ) := by
  let a := List.ofFn (fun i : Fin (p.natDegree+1) ↦ p.coeff i.val)
  refine ⟨a, denote_ofRatList_eq a p ?_⟩
  intro k
  by_cases hk : k < p.natDegree+1
  · rw [List.getD_eq_getElem a 0 (by simpa [a] using hk)]
    simp only [a, List.getElem_ofFn]
  · rw [List.getD_eq_default a 0 (by simpa [a] using le_of_not_gt hk),
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

/-- Exact Gaussian-rational evaluation of a literal rational coefficient list. -/
def evaluateRatList (a : List ℚ) (c : GaussianRational) : GaussianRational :=
  taylorCoefficient (ofRatList a) c 0

theorem evaluateRatList_correct (a : List ℚ) (c : GaussianRational) :
    toComplex (evaluateRatList a c) = (denote (ofRatList a)).eval (toComplex c) := by
  rw [evaluateRatList, taylorCoefficient_correct, Polynomial.taylor_coeff_zero]

/-- The selected common-field defining polynomial, with its leading one implicit. -/
def ofMonicIntTail {n : ℕ} (a : Fin n → ℤ) : Code n :=
  fun i ↦ if h : i.val < n then ⟨(a ⟨i.val,h⟩ : ℚ),0⟩ else
    if i.val = n then 1 else 0

def rootCertificateMonicTail {n : ℕ} (a : Fin n → ℤ)
    (c : GaussianRational) (r : ℚ) : Bool := rootCertificate (ofMonicIntTail a) c r

/-- A rational coordinate vector denotes its ordinary degree-bounded polynomial. -/
def ofRatVector {n : ℕ} (a : Fin n → ℚ) : Code n :=
  fun i ↦ if h : i.val < n then ⟨a ⟨i.val,h⟩,0⟩ else 0

def imageCertificateRatVector {n : ℕ} (a : Fin n → ℚ)
    (c : GaussianRational) (r : ℚ) (box : Rectangle) : Bool :=
  imageCertificate (ofRatVector a) c r box

def evaluateRatVector {n : ℕ} (a : Fin n → ℚ) (c : GaussianRational) : GaussianRational :=
  taylorCoefficient (ofRatVector a) c 0

theorem denote_ofMonicIntTail_eq {n : ℕ} (a : Fin n → ℤ) (p : Polynomial ℤ)
    (hp : p.Monic) (hd : p.natDegree = n) (hc : ∀ i : Fin n, p.coeff i.val = a i) :
    denote (ofMonicIntTail a) = p.map (Int.castRingHom ℂ) := by
  apply Polynomial.ext
  intro k
  rw [denote_coeff, Polynomial.coeff_map]
  by_cases hk : k < n
  · rw [dif_pos (by omega)]
    simp only [ofMonicIntTail, hk, ↓reduceDIte]
    rw [hc ⟨k,hk⟩]
    apply Complex.ext <;> simp [toComplex]
  · by_cases he : k = n
    · subst k
      rw [dif_pos (by omega)]
      simp only [ofMonicIntTail, lt_self_iff_false, ↓reduceDIte, ↓reduceIte, map_one]
      rw [← hd, hp.coeff_natDegree]
      simp
    · have hz : p.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
      rw [hz, map_zero]
      by_cases hkn : k < n+2
      · rw [dif_pos hkn]
        simp [ofMonicIntTail, hk, he]
      · rw [dif_neg hkn]

@[simp] theorem denote_ofRatVector_coeff {n : ℕ} (a : Fin n → ℚ) (k : ℕ) :
    (denote (ofRatVector a)).coeff k = if h : k < n then (a ⟨k,h⟩ : ℂ) else 0 := by
  rw [denote_coeff]
  by_cases hk : k < n
  · rw [dif_pos (by omega), dif_pos hk]
    simp only [ofRatVector, hk, ↓reduceDIte]
    apply Complex.ext <;> simp [toComplex]
  · rw [dif_neg hk]
    by_cases hkn : k < n+2
    · rw [dif_pos hkn]
      simp [ofRatVector, hk]
    · rw [dif_neg hkn]

theorem eval_denote_ofRatVector {n : ℕ} (a : Fin n → ℚ) (z : ℂ) :
    (denote (ofRatVector a)).eval z = ∑ i : Fin n, (a i : ℂ)*z^i.val := by
  rw [Polynomial.eval_eq_sum_range' (denote_degree_bound _), Finset.sum_range]
  simp only [denote_ofRatVector_coeff]
  rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [Fin.val_last, Fin.coe_castSucc, lt_self_iff_false, ↓reduceDIte, zero_mul,
    show ¬n+1 < n by omega, add_zero]
  apply Finset.sum_congr rfl
  intro i _
  rw [dif_pos i.isLt]

 theorem evaluateRatVector_correct {n : ℕ} (a : Fin n → ℚ) (c : GaussianRational) :
    toComplex (evaluateRatVector a c) = ∑ i : Fin n, (a i : ℂ)*(toComplex c)^i.val := by
  rw [evaluateRatVector, taylorCoefficient_correct, Polynomial.taylor_coeff_zero,
    eval_denote_ofRatVector]

end ComplexCSP.ComplexRootCertificates
