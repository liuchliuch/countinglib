import ComplexCSP.Algebra.PositiveGramPower
import ComplexCSP.Algebra.PositiveGramPowerGadget

/-! # Ordered-real coefficient fields and the compiled positive-power reduction -/
noncomputable section
open Classical
namespace ComplexCSP.PositiveGramPowerField
open scoped BigOperators
open PlanarHom PlanarHom.Complexity ComplexityReducedGram
variable {I : Type} [Fintype I] (K : IntermediateField ℚ ℝ) (A : Matrix I I K)

def realMatrix : Matrix I I ℝ := fun i j => (A i j : ℝ)

theorem real_pow (n : ℕ) (i j : I) : ((A^n) i j : ℝ)=(realMatrix K A ^ n) i j := by
  have h := congrArg (fun M : Matrix I I ℝ => M i j) ((K.subtype.mapMatrix).map_pow A n)
  exact h

def StrictMinor (i j : I) : Prop :=
  0<A i i ∧ 0<A i j ∧ 0<A j j ∧ A i j*A j i < A i i*A j j

/-- The exact same explicit exponent and strict pair hold in the actual real
subfield's induced order. No coordinate-order algorithm is used or assumed. -/
theorem positive_power_and_minor
    (hA : ∀ i j,0≤A i j) (hd : ∀ i,0<A i i)
    (hc : ∀ i j,Relation.ReflTransGen (fun x y => 0<A x y) i j)
    (hs : ∀ i j,A i j=A j i) (i j : I) (hm : StrictMinor K A i j) :
    (∀ x y,0<(A^(2^Fintype.card I)) x y) ∧ StrictMinor K (A^(2^Fintype.card I)) i j := by
  have hm' : PositiveGramPower.StrictMinor (realMatrix K A) i j := hm
  have hs' : ∀ i j,realMatrix K A i j=realMatrix K A j i :=
    fun i j => congrArg (fun x : K => (x : ℝ)) (hs i j)
  have h := PositiveGramPower.positive_power_and_minor (realMatrix K A) hA hd hc hs' i j hm'
  constructor
  · intro x y
    change 0<((A^(2^Fintype.card I)) x y : ℝ)
    rw [real_pow]
    exact h.1 x y
  · change 0<((A^(2^Fintype.card I)) i i : ℝ) ∧
      0<((A^(2^Fintype.card I)) i j : ℝ) ∧
      0<((A^(2^Fintype.card I)) j j : ℝ) ∧
      ((A^(2^Fintype.card I)) i j : ℝ)*((A^(2^Fintype.card I)) j i : ℝ) <
        ((A^(2^Fintype.card I)) i i : ℝ)*((A^(2^Fintype.card I)) j j : ℝ)
    simpa only [real_pow, PositiveGramPower.StrictMinor] using h.2

/-- The actual fixed-path machine for the same explicit positive power. -/
def reduction {d : ℕ} (basis : Module.Basis (Fin d) ℚ K) :
    PromisePolyTimeTuringReduction
      (ComplexityCSPCountReduction.partitionProblem (binaryLanguage (A^(2^Fintype.card I))) basis)
      (ComplexityCSPCountReduction.partitionProblem (binaryLanguage A) basis) :=
  PositiveGramPowerGadget.positiveReduction A basis (2^Fintype.card I) (by positivity)

end ComplexCSP.PositiveGramPowerField
