import Paper2.RelativeEO.BinaryEOArithmetic
import Paper2.PrimeFactorization.PointMass

/-! Exact ordered binary EO forms and their singular tensor factorizations. -/
namespace Paper2.RelativeEO
open Paper2.Tractable

def binWord (a b : Bool) : Fin 2 → Bool := Fin.cases a (fun _ => b)

theorem binWord_eta (x : Fin 2 → Bool) : binWord (x 0) (x 1) = x := by
  funext i
  fin_cases i <;> rfl

noncomputable def pinAmplitude (b : Bool) (c : AlgebraicComplex) : Signature AlgebraicComplex 1 :=
  fun x => if x 0 = b then c else 0

theorem pinAmplitude_ne_zero (b : Bool) (c : AlgebraicComplex) (hc : c ≠ 0) :
    pinAmplitude b c ≠ 0 := by
  intro hz
  have h := congrFun hz (fun _ => b)
  simp only [pinAmplitude, ite_true, Pi.zero_apply] at h
  exact hc h

theorem eoSignature_left_zero (b : AlgebraicComplex) :
    eoSignature 0 b = Signature.tensor (pinAmplitude true b) (TensorDecomposition.literalPin false) := by
  funext x
  change (if x 0 then (if x 1 then (0 : AlgebraicComplex) else b) else (if x 1 then 0 else 0)) =
    (if x 0 = true then b else 0) * (if x 1 = false then 1 else 0)
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [h0, h1]

theorem eoSignature_right_zero (a : AlgebraicComplex) :
    eoSignature a 0 = Signature.tensor (pinAmplitude false a) (TensorDecomposition.literalPin true) := by
  funext x
  change (if x 0 then (if x 1 then (0 : AlgebraicComplex) else 0) else (if x 1 then a else 0)) =
    (if x 0 = false then a else 0) * (if x 1 = true then 1 else 0)
  cases h0 : x 0 <;> cases h1 : x 1 <;> simp [h0, h1]

@[simp] theorem eoSignature_zero : eoSignature 0 0 = 0 := by
  funext x
  simp [eoSignature, matrixSignature, eoMatrix]

/-- Arity-two central support forces exactly the two off-diagonal entries,
without any symmetry, conjugacy, reality, or nonzero promise on those entries. -/
theorem binary_central_form (f : Signature AlgebraicComplex 2) (h : Signature.CentralSupport f) :
    f = eoSignature (f (binWord false true)) (f (binWord true false)) := by
  have h00 : f (binWord false false) = 0 := h _ (by decide)
  have h11 : f (binWord true true) = 0 := h _ (by decide)
  funext x
  conv_lhs => rw [← binWord_eta x]
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [eoSignature, matrixSignature, eoMatrix, h0, h1, h00, h11]

end Paper2.RelativeEO
