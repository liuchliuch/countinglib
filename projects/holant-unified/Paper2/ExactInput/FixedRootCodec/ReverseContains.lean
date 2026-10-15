import Paper2.ExactInput.FixedRootCodec.ReverseSign
import Paper2.ExactInput.FixedRootCodec.IsolatingRectangle

/-! Exact strict rectangle membership for fixed-field candidates. Boundary
equality is handled by the exact algebraic sign program, so no proximity
promise about the supplied rational rectangle is required. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open scoped BigOperators
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} (a : Fin n → ℝ) (ha : ∀ i, IsAlgebraic ℚ (a i))

def upperComparisonCoefficients : Fin (n+1) → ℝ := Fin.cons (-1) a
def lowerComparisonCoefficients : Fin (n+1) → ℝ := Fin.cons 1 (fun i => -a i)

include ha in
theorem upperComparison_algebraic : ∀ i, IsAlgebraic ℚ (upperComparisonCoefficients a i) := by
  intro i
  refine Fin.cases ?_ (fun j => ha j) i
  simpa [upperComparisonCoefficients] using (isAlgebraic_algebraMap (-1 : ℚ) :
    IsAlgebraic ℚ (algebraMap ℚ ℝ (-1)))

include ha in
theorem lowerComparison_algebraic : ∀ i, IsAlgebraic ℚ (lowerComparisonCoefficients a i) := by
  intro i
  refine Fin.cases ?_ (fun j => (ha j).neg) i
  simpa [lowerComparisonCoefficients] using (isAlgebraic_algebraMap (1 : ℚ) :
    IsAlgebraic ℚ (algebraMap ℚ ℝ 1))

theorem upperComparison_value (q : ℚ) (v : Fin n → ℚ) :
    realLinearValue (upperComparisonCoefficients a) (Fin.cons q v)=realLinearValue a v-(q : ℝ) := by
  simp [realLinearValue,upperComparisonCoefficients,Fin.sum_univ_succ]
  ring

theorem lowerComparison_value (q : ℚ) (v : Fin n → ℚ) :
    realLinearValue (lowerComparisonCoefficients a) (Fin.cons q v)=(q : ℝ)-realLinearValue a v := by
  simp [realLinearValue,lowerComparisonCoefficients,Fin.sum_univ_succ,Finset.sum_neg_distrib]
  ring

def realLinearUpperComputes : Computes (pairEncoding rationalEncoding (vectorEncoding n))
    encodingBoolBool (fun p => decide (realLinearValue a p.2<(p.1 : ℝ))) := by
  apply recode (realLinearNegativeComputes (upperComparisonCoefficients a) (upperComparison_algebraic a ha))
    (fun p => Fin.cons p.1 p.2) (fun _ => rfl)
  intro p
  apply congrArg encodingBoolBool.encode
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,upperComparison_value]
  exact sub_neg

def realLinearLowerComputes : Computes (pairEncoding rationalEncoding (vectorEncoding n))
    encodingBoolBool (fun p => decide ((p.1 : ℝ)<realLinearValue a p.2)) := by
  apply recode (realLinearNegativeComputes (lowerComparisonCoefficients a) (lowerComparison_algebraic a ha))
    (fun p => Fin.cons p.1 p.2) (fun _ => rfl)
  intro p
  apply congrArg encodingBoolBool.encode
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,lowerComparison_value]
  exact sub_neg

def boolAndComputes {A : Type} {e : Encoding A Bool} {p q : A → Bool}
    (u : Computes e encodingBoolBool p) (v : Computes e encodingBoolBool q) :
    Computes e encodingBoolBool (fun x => p x && q x) :=
  congrComputes (ifComputes u v (constantComputes e encodingBoolBool false))
    (fun x => by cases h : p x <;> simp [h])

abbrev rectangleFourEncoding := pairEncoding rationalEncoding
  (pairEncoding rationalEncoding (pairEncoding rationalEncoding rationalEncoding))

def rectangleTupleComputes : Computes rectangleEncoding rectangleFourEncoding
    (fun r => (r.reLower,r.reUpper,r.imLower,r.imUpper)) :=
  recode (identityComputes rectangleFourEncoding)
    (fun r => (r.reLower,r.reUpper,r.imLower,r.imUpper)) (fun _ => rfl) (fun _ => rfl)

variable {K : Type} [Field K] [Algebra ℚ K]

def fieldRectangleContainsComputes (F : FixedField K n) (e : K →ₐ[ℚ] ℂ) :
    Computes (pairEncoding (vectorEncoding n) rectangleEncoding) encodingBoolBool
      (fun p => decide (p.2.Contains (e (F.decode p.1)))) := by
  let ar := fun i => (complexBasis F e i).re
  let ai := fun i => (complexBasis F e i).im
  have har : ∀ i, IsAlgebraic ℚ (ar i) := fun i => algebraic_re _ (complexBasis_algebraic F e i)
  have hai : ∀ i, IsAlgebraic ℚ (ai i) := fun i => algebraic_im _ (complexBasis_algebraic F e i)
  let v := Wiring.firstComputes (vectorEncoding n) rectangleEncoding
  let r := (Wiring.secondComputes (vectorEncoding n) rectangleEncoding).andThen rectangleTupleComputes
  let rl := r.andThen (Wiring.firstComputes rationalEncoding
    (pairEncoding rationalEncoding (pairEncoding rationalEncoding rationalEncoding)))
  let tail := r.andThen (Wiring.secondComputes rationalEncoding
    (pairEncoding rationalEncoding (pairEncoding rationalEncoding rationalEncoding)))
  let ru := tail.andThen (Wiring.firstComputes rationalEncoding (pairEncoding rationalEncoding rationalEncoding))
  let rest := tail.andThen (Wiring.secondComputes rationalEncoding (pairEncoding rationalEncoding rationalEncoding))
  let il := rest.andThen (Wiring.firstComputes rationalEncoding rationalEncoding)
  let iu := rest.andThen (Wiring.secondComputes rationalEncoding rationalEncoding)
  let hreLower := (pairComputes rl v).andThen (realLinearLowerComputes ar har)
  let hreUpper := (pairComputes ru v).andThen (realLinearUpperComputes ar har)
  let himLower := (pairComputes il v).andThen (realLinearLowerComputes ai hai)
  let himUpper := (pairComputes iu v).andThen (realLinearUpperComputes ai hai)
  apply congrComputes (boolAndComputes hreLower (boolAndComputes hreUpper (boolAndComputes himLower himUpper)))
  intro p
  have hr : realLinearValue ar p.1=(e (F.decode p.1)).re := by
    simpa only [realLinearValue,ar,complexLinearValue_re] using
      congrArg Complex.re (complexBasis_value F e p.1)
  have hi : realLinearValue ai p.1=(e (F.decode p.1)).im := by
    simpa only [realLinearValue,ai,complexLinearValue_im] using
      congrArg Complex.im (complexBasis_value F e p.1)
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply,Bool.and_eq_true,decide_eq_true_eq,hr,hi]
  rfl

end
end Paper2.ExactInput.FixedRootCodec
