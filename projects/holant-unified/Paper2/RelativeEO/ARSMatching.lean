import Paper2.RelativeEO.BinaryEOAlternative
import Paper2.WeightedMatching

/-! Literal B_ARS of Paper 2 §3.3. The overall scalar is arbitrary nonzero
algebraic; each oriented binary factor has the exact conjugate pair (a,conj a).
This file also closes the arity-two case of the relative terminal theorem. -/
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open scoped BigOperators

/-- Exact arrow reversal, over the actual algebraic coefficient field. -/
def ARS {n : ℕ} (f : Signature AlgebraicComplex n) : Prop :=
  ∀ x, (f x : ℂ) = star (f (fun i => !(x i)) : ℂ)

/-- Exactly the prohibited decomposition in source Theorem 3.7. Every port
occurs once in the oriented matching and every displayed scalar is nonzero. -/
def IsARSProduct {n : ℕ} (f : Signature AlgebraicComplex n) : Prop :=
  ∃ (P : OrientedPerfectPairing n) (a : Fin P.count → AlgebraicComplex)
    (c : AlgebraicComplex), c ≠ 0 ∧ (∀ j, a j ≠ 0) ∧
      f = WeightedMatching.product P a (fun j => conjugateAlgebraic (a j)) c

@[simp] theorem conjugateAlgebraic_ne_zero {z : AlgebraicComplex} :
    conjugateAlgebraic z ≠ 0 ↔ z ≠ 0 := by
  have h₁ : conjugateAlgebraic z = 0 ↔ star (z : ℂ) = 0 := by
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  have h₂ : z = 0 ↔ (z : ℂ) = 0 := by
    constructor
    · intro h; exact congrArg Subtype.val h
    · intro h; exact Subtype.ext h
  simp only [ne_eq, h₁, star_eq_zero, h₂]

/-- The broader matching class B_× contains B_ARS, with exactly the same
oriented pairing. In particular a proved B_× counterexample suffices at 3.7. -/
theorem IsARSProduct.isProduct {n : ℕ} {f : Signature AlgebraicComplex n}
    (h : IsARSProduct f) : WeightedMatching.IsProduct f := by
  obtain ⟨P,a,c,hc,ha,hf⟩ := h
  refine ⟨P,a,(fun j => conjugateAlgebraic (a j)),c,?_,hf⟩
  exact mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr
    (fun j _ => mul_ne_zero (ha j) (conjugateAlgebraic_ne_zero.mpr (ha j))))

/-- A canonical one-pair matching, preserving first and second binary ports. -/
def binaryPairing : OrientedPerfectPairing 2 where
  count := 1
  ports := {
    toFun := fun p => if p.2 then 1 else 0
    invFun := fun i => (0, i == 1)
    left_inv := by rintro ⟨j,b⟩; have hj : j = 0 := Fin.eq_zero j; subst j; cases b <;> rfl
    right_inv := by intro i; fin_cases i <;> rfl }

@[simp] theorem binaryPairing_product (a b c : AlgebraicComplex) :
    WeightedMatching.product binaryPairing (fun _ => a) (fun _ => b) c =
      fun x => c * eoSignature a b x := by
  funext x
  change c * (∏ _j : Fin 1, WeightedMatching.binary a b (x 0) (x 1)) = _
  rw [Fin.prod_univ_one]
  rfl

/-- A nonzero EO binary which is projectively ARS is literally an algebraic
scalar times one exact ARS binary. No positive-order promise is required. -/
theorem binary_arsProduct (f : Signature AlgebraicComplex 2) (hf : f ≠ 0)
    (hEO : Signature.CentralSupport f) (hARS : ProjectiveARS f) : IsARSProduct f := by
  obtain ⟨c,hc,hs⟩ := hARS
  let a := f (binWord false true)
  let b := f (binWord true false)
  have hform : f = eoSignature a b := binary_central_form f hEO
  have hcomp : (fun i => !(binWord true false i)) = binWord false true := by
    funext i; fin_cases i <;> rfl
  have ha : a ≠ 0 := by
    intro ha
    have hab := hs (binWord true false)
    rw [hcomp] at hab
    have hz : (b : ℂ) = 0 := by
      have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
      change (c : ℂ)⁻¹ * (b : ℂ) = star ((c : ℂ)⁻¹ * (a : ℂ)) at hab
      rw [ha] at hab
      simpa only [ZeroMemClass.coe_zero, mul_zero, star_zero, mul_eq_zero,
        inv_eq_zero, hcC, false_or] using hab
    have hb : b = 0 := Subtype.ext hz
    exact hf (by rw [hform,ha,hb,eoSignature_zero])
  let z := c⁻¹ * a
  have hz : z ≠ 0 := mul_ne_zero (inv_ne_zero hc) ha
  have hba : c⁻¹ * b = conjugateAlgebraic z := by
    apply Subtype.ext
    change (c : ℂ)⁻¹ * (b : ℂ) = star ((c : ℂ)⁻¹ * (a : ℂ))
    simpa only [hcomp] using hs (binWord true false)
  have ha' : c * z = a := by dsimp [z]; rw [← mul_assoc,mul_inv_cancel₀ hc,one_mul]
  have hb' : c * conjugateAlgebraic z = b := by
    rw [← hba,← mul_assoc,mul_inv_cancel₀ hc,one_mul]
  refine ⟨binaryPairing,(fun _ => z),c,hc,(fun _ => hz),?_⟩
  rw [binaryPairing_product,hform]
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [eoSignature,matrixSignature,eoMatrix,h0,h1,ha',hb']

/-- The source relative terminal is fully proved for an arity-two EO member,
using only the exact cited Paper 1 interpolation/factor/unary inputs. -/
theorem binary_relative_terminal (P : Paper1BinaryInterpolationAccepted)
    (F : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted) (L : Language)
    (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) (f : Signature AlgebraicComplex 2)
    (hf : f ≠ 0) (hEO : Signature.CentralSupport f)
    (hmem : (⟨2,f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hout : ¬ IsARSProduct f) : SharpPHard .nativeX L := by
  rcases binary_eo_alternative P F U L hpre hboth hnot f hf hEO hmem with hs | hh
  · exact False.elim (hout (binary_arsProduct f hf hEO hs))
  · exact hh

end Paper2.RelativeEO
