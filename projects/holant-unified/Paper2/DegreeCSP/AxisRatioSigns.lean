import Paper2.Tractable.Affine
import Mathlib.Algebra.Ring.Commute
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! Exact coefficient reconstruction from squared coordinate-edge ratios.
The hypercube is traversed by support-set induction, and the remaining scalar
is an actual sign. No closure, classification or hardness premise is supplied. -/
namespace Paper2.DegreeCSP.AxisRatioSigns
open scoped BigOperators
noncomputable section
set_option maxHeartbeats 600000

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

def zeroWord : ι → Bool := fun _=>false

def axisRatio (f : (ι → Bool) → K) (i : ι) : K :=
  f (Function.update zeroWord i true) / f zeroWord

def wordFactor (φ : ι → K) (x : ι → Bool) : K :=
  ∏ i,if x i then φ i else 1

@[simp] theorem wordFactor_zeroWord (φ : ι → K) : wordFactor φ zeroWord = 1 := by
  simp [wordFactor,zeroWord]

theorem axisRatio_ne_zero (f : (ι → Bool) → K) (hf : ∀x,f x≠0) (i : ι) :
    axisRatio f i≠0 := div_ne_zero (hf _) (hf _)

theorem wordFactor_ne_zero (φ : ι → K) (hφ : ∀i,φ i≠0) (x : ι → Bool) :
    wordFactor φ x≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  cases x i <;> simp [hφ]

private def subsetWord (S : Finset ι) : ι → Bool := fun i=>decide (i∈S)

private theorem subsetWord_empty : (subsetWord (∅ : Finset ι)) = zeroWord := by
  funext i
  simp [subsetWord,zeroWord]

private theorem subsetWord_insert (S : Finset ι) (i : ι) :
    subsetWord (insert i S)=Function.update (subsetWord S) i true := by
  funext j
  by_cases h : j=i
  · subst j
    simp [subsetWord]
  · simp [subsetWord,Function.update,h]

/-- The precise squared coefficient identity follows by adding the supported
coordinates one at a time. The result includes the empty coordinate set. -/
theorem square_factorization (f : (ι → Bool) → K) (φ : ι → K)
    (hedge : ∀i x,x i=false →
      f (Function.update x i true)^2=φ i^2*f x^2) (x : ι → Bool) :
    f x^2=(f zeroWord*wordFactor φ x)^2 := by
  have hS : ∀S : Finset ι,
      f (subsetWord S)^2=(f zeroWord*(∏i∈S,φ i))^2 := by
    intro S
    induction S using Finset.induction_on with
    | empty => simp [subsetWord_empty]
    | @insert i S hi ih =>
      rw [subsetWord_insert,hedge i (subsetWord S) (by simp [subsetWord,hi]),ih,
        Finset.prod_insert hi]
      ring
  let S := Finset.univ.filter (fun i=>x i=true)
  have hword : subsetWord S=x := by
    funext i
    simp [S,subsetWord]
  have hfactor : (∏i∈S,φ i)=wordFactor φ x := by
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    cases x i <;> rfl
  simpa only [hword,hfactor] using hS S

/-- The normalized quotient is a square root of one. Its denominator is proved
nonzero from the actual full-support coefficient family. -/
theorem normalized_square (f : (ι → Bool) → K) (φ : ι → K)
    (hf : ∀x,f x≠0) (hφ : ∀i,φ i≠0)
    (hedge : ∀i x,x i=false →
      f (Function.update x i true)^2=φ i^2*f x^2) (x : ι → Bool) :
    (f x/(f zeroWord*wordFactor φ x))^2=1 := by
  rw [div_pow,square_factorization f φ hedge x]
  exact div_self (pow_ne_zero 2 (mul_ne_zero (hf _) (wordFactor_ne_zero φ hφ x)))

/-- An explicit Boolean sign choice reconstructs every coefficient, including
arity zero. The scalar and all coordinate factors stay in the original field. -/
theorem signs_of_edge_squares (f : (ι → Bool) → K) (φ : ι → K)
    (hedge : ∀i x,x i=false →
      f (Function.update x i true)^2=φ i^2*f x^2) :
    ∃P : (ι → Bool) → Bool,P zeroWord=false ∧ ∀x,
      f x=f zeroWord*wordFactor φ x*(if P x then -1 else 1) := by
  classical
  let P : (ι → Bool) → Bool := fun x=>decide (f x≠f zeroWord*wordFactor φ x)
  refine ⟨P,?_,?_⟩
  · simp [P]
  · intro x
    have h := sq_eq_sq_iff_eq_or_eq_neg.mp (square_factorization f φ hedge x)
    rcases h with h|h
    · simp [P,h]
    · by_cases he : f x=f zeroWord*wordFactor φ x
      · simp [P,he]
      · simp [P,he,h]

theorem signs_of_squared_edge_ratios (f : (ι → Bool) → K)
    (hf : ∀x,f x≠0)
    (hedge : ∀i x,x i=false →
      f (Function.update x i true)^2=axisRatio f i^2*f x^2) :
    (∀i,axisRatio f i≠0) ∧ ∃P : (ι → Bool) → Bool,P zeroWord=false ∧ ∀x,
      f x=f zeroWord*(∏i,if x i then axisRatio f i else 1)*(if P x then -1 else 1) := by
  exact ⟨axisRatio_ne_zero f hf,signs_of_edge_squares f (axisRatio f) hedge⟩

end
end Paper2.DegreeCSP.AxisRatioSigns
