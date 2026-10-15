import Paper2.Complexity.BellMachines.BoundedIterateRestricted
import Paper2.Complexity.BellMachines.FieldArithmetic

/-! Unary powers of a fixed field element by a real finite multiplication loop.
Intermediate canonical coordinate lengths are bounded using the proved fixed
family product theorem, so the time bound is polynomial rather than an iterated
composition of polynomials. -/
namespace Paper2.Complexity.BellMachines
open Computability BinaryCompose FixedFieldMachines GraphPreprocessing Paper2.Algebraic
open scoped BigOperators
noncomputable section
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}

 def powerPolynomial (F : FixedField K d) (c : K) : Polynomial ℕ :=
  let coeff : Unit → Fin d → ℚ := fun _ => F.basis.equivFun c
  let M := F.toArithmeticData.familyBound coeff
  let D := F.toArithmeticData.familyDenominator coeff
  Polynomial.C d * (4 * (Polynomial.C M.size +
    Polynomial.X * Polynomial.C (d*d*M*M).size +
    (2*Polynomial.X+1)*Polynomial.C D.size+3)+1)

 theorem power_length (F : FixedField K d) (c : K) (n : ℕ) :
    (F.encoding.encode (c^n)).length ≤ (powerPolynomial F c).eval n := by
  let coeff : Unit → Fin d → ℚ := fun _ => F.basis.equivFun c
  have h := F.sumProducts_answer_length_le_exponential coeff
    (fun (_ : Fin 1) (_ : Fin n) => ()) (e := 0) (by simp)
  simpa [coeff,powerPolynomial,FixedField.decode] using h

 theorem iterate_scale_one (c : K) (n : ℕ) :
    ((fun x : K => x*c)^[n]) 1 = c^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply',ih,pow_succ]

 def powerComputes (F : FixedField K d) (c : K) :
    Computes UnaryBinary.unaryEncoding F.encoding (fun n => c^n) := by
  classical
  let p : ℕ × K → Prop := fun x => x.2 = 1
  let initial (n : ℕ) : {x : ℕ × K // p x} := ⟨(n,1),rfl⟩
  let prepare : Computes UnaryBinary.unaryEncoding (BoundedIterate.restrictedEncoding F.encoding p) initial :=
    recode (pairComputes (identityComputes UnaryBinary.unaryEncoding)
      (constantComputes UnaryBinary.unaryEncoding F.encoding 1)) id (fun _ => rfl) (fun _ => rfl)
  let step := scaleComputes F (identityComputes F.encoding) c
  have hb : ∀ (x : {x : ℕ × K // p x}) (k : ℕ), k ≤ x.val.1 →
      (F.encoding.encode (((fun y : K => y*c)^[k]) x.val.2)).length ≤
        (powerPolynomial F c).eval ((BoundedIterate.restrictedEncoding F.encoding p).encode x).length := by
    intro x k hk
    have hx : x.val.2 = 1 := x.property
    rw [hx,iterate_scale_one]
    apply (power_length F c k).trans
    apply natPolynomial_eval_mono
    have hn : x.val.1 ≤ ((BoundedIterate.restrictedEncoding F.encoding p).encode x).length := by
      simp [BoundedIterate.restrictedEncoding,BoundedIterate.inputEncoding,pairEncoding,
        UnaryBinary.unaryEncoding]
      omega
    exact hk.trans hn
  let run := BoundedIterate.restrictedComputes F.encoding (fun y : K => y*c) step p (powerPolynomial F c) hb
  exact congrComputes (prepare.andThen run) (fun n => iterate_scale_one c n)

/-- The nonzero scalar inverse is fixed program data. -/
 def inversePowerComputes (F : FixedField K d) (c : K) :
    Computes UnaryBinary.unaryEncoding F.encoding (fun n => (c^n)⁻¹) :=
  congrComputes (powerComputes F c⁻¹) (fun n => inv_pow c n)

 def correctByPowerComputes (F : FixedField K d) (c : K) :
    Computes (pairEncoding UnaryBinary.unaryEncoding F.encoding) F.encoding
      (fun p => p.2 / c^p.1) := by
  let power := (Wiring.firstComputes UnaryBinary.unaryEncoding F.encoding).andThen
    (inversePowerComputes F c)
  let value := Wiring.secondComputes UnaryBinary.unaryEncoding F.encoding
  exact congrComputes ((pairComputes value power).andThen (fieldMultiplication F))
    (fun p => (div_eq_mul_inv p.2 (c^p.1)).symm)

end
end Paper2.Complexity.BellMachines
