import ComplexCSP.Complexity.TypeStackCall
import PlanarHom.BoundedIterationMachine
import PlanarHom.InputLengthMachine

/-! # Actual polynomial-time capped iteration on immutable context

The cap is a physically present unary input, checked by the real input-length
machine. It bounds every raw execution, including malformed states. Correctness
for the intended uncapped run is a separate no-cap-trigger theorem, discharged
using the actual source-instance semantic size invariants.
-/
namespace ComplexCSP.ComplexityCappedIteration
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityTypeStackMachines
variable {C S : Type}

abbrev Configuration (C S : Type) := C × (ℕ × S)
def configurationCode (ec : BitEncoding C) (es : BitEncoding S) : BitEncoding (Configuration C S) :=
  ec.prod (BitEncoding.unaryNat.prod es)

def next (transition : C × S → Option S) (p : C × S) : S := (transition p).getD p.2

def limitedStep (es : BitEncoding S) (fallback : S) (transition : C × S → Option S)
    (p : Configuration C S) : Configuration C S :=
  let candidate := next transition (p.1,p.2.2)
  (p.1,p.2.1,if (es.encode candidate).length ≤ p.2.1 then candidate else fallback)

theorem fp_next (ec : BitEncoding C) (es : BitEncoding S) (fallback : S)
    (transition : C × S → Option S) (ht : FP (ec.prod es) (optionCode es) transition) :
    FP (ec.prod es) es (next transition) := by
  have hn := ht.comp (fp_isNone es)
  have hv := ht.comp (fp_optionGetD es fallback)
  apply (fp_boolChoice _ _ hn (fp_snd ec es) hv).congr
  intro p
  unfold next
  cases h : transition p <;> simp [h]

theorem fp_limitedStep (ec : BitEncoding C) (es : BitEncoding S) (fallback : S)
    (transition : C × S → Option S) (ht : FP (ec.prod es) (optionCode es) transition) :
    FP (configurationCode ec es) (configurationCode ec es) (limitedStep es fallback transition) := by
  let inputCode := configurationCode ec es
  have hc := fp_fst ec (BitEncoding.unaryNat.prod es)
  have hr := fp_snd ec (BitEncoding.unaryNat.prod es)
  have hb := hr.comp (fp_fst BitEncoding.unaryNat es)
  have hs := hr.comp (fp_snd BitEncoding.unaryNat es)
  have hv := (hc.pair hs).comp (fp_next ec es fallback transition ht)
  have hl : FP es BitEncoding.unaryNat (fun s => (es.encode s).length) :=
    ⟨InputLengthMachine.computer es⟩
  have hvlen := (hv.comp hl).comp UnaryNatConversionMachine.fp_conversion
  have hbnat := hb.comp UnaryNatConversionMachine.fp_conversion
  have hlarge := (hbnat.pair hvlen).comp BinaryArithmetic.fp_comparison
  have hselected := hlarge.ite (fp_const inputCode es fallback) hv
  apply (hc.pair (hb.pair hselected)).congr
  intro p
  dsimp only [Function.comp_apply, limitedStep, id_eq]
  by_cases h : (es.encode (next transition (p.1,p.2.2))).length ≤ p.2.1
  · simp [h, Nat.not_lt.mpr h]
  · simp [h, Nat.lt_of_not_ge h]

@[simp] theorem limitedStep_context (es : BitEncoding S) (fallback : S)
    (transition : C × S → Option S) (p : Configuration C S) :
    (limitedStep es fallback transition p).1 = p.1 := rfl
@[simp] theorem limitedStep_budget (es : BitEncoding S) (fallback : S)
    (transition : C × S → Option S) (p : Configuration C S) :
    (limitedStep es fallback transition p).2.1 = p.2.1 := rfl

theorem limitedStep_state_bound (es : BitEncoding S) (fallback : S)
    (transition : C × S → Option S) (p : Configuration C S) :
    (es.encode (limitedStep es fallback transition p).2.2).length ≤
      p.2.1 + (es.encode fallback).length := by
  unfold limitedStep
  dsimp only
  split <;> omega

@[simp] theorem iterate_context (es : BitEncoding S) (fallback : S)
    (transition : C × S → Option S) (p : Configuration C S) (i : ℕ) :
    ((limitedStep es fallback transition)^[i] p).1 = p.1 := by
  induction i with
  | zero => rfl
  | succ i ih => simpa only [Function.iterate_succ_apply',limitedStep_context] using ih

@[simp] theorem iterate_budget (es : BitEncoding S) (fallback : S)
    (transition : C × S → Option S) (p : Configuration C S) (i : ℕ) :
    ((limitedStep es fallback transition)^[i] p).2.1 = p.2.1 := by
  induction i with
  | zero => rfl
  | succ i ih => simpa only [Function.iterate_succ_apply',limitedStep_budget] using ih

/-- Explicit linear intermediate bound, with both unary counters fully charged. -/
theorem iterate_code_bound (ec : BitEncoding C) (es : BitEncoding S) (fallback : S)
    (transition : C × S → Option S) (count : ℕ) (p : Configuration C S) (i : ℕ) :
    ((configurationCode ec es).encode ((limitedStep es fallback transition)^[i] p)).length ≤
      (Polynomial.C 3*Polynomial.X + Polynomial.C ((es.encode fallback).length+2)).eval
        ((BitEncoding.unaryNat.prod (configurationCode ec es)).encode (count,p)).length := by
  let N := ((BitEncoding.unaryNat.prod (configurationCode ec es)).encode (count,p)).length
  have hN : N = 2*count + (2*(ec.encode p.1).length +
      (2*p.2.1+(es.encode p.2.2).length+1)+1)+1 := by
    simp only [N, configurationCode, BitEncoding.prod_length, BitEncoding.unaryNat_length]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]
  change _ ≤ 3*N + ((es.encode fallback).length+2)
  cases i with
  | zero =>
    simp only [Function.iterate_zero, id_eq, configurationCode, BitEncoding.prod_length,
      BitEncoding.unaryNat_length]
    omega
  | succ i =>
    have hs := limitedStep_state_bound es fallback transition
      ((limitedStep es fallback transition)^[i] p)
    rw [iterate_budget] at hs
    have hc := iterate_context es fallback transition p (i+1)
    have hb := iterate_budget es fallback transition p (i+1)
    rw [configurationCode, BitEncoding.prod_length, BitEncoding.prod_length]
    rw [hc,hb,BitEncoding.unaryNat_length]
    rw [Function.iterate_succ_apply']
    omega

/-- An actual finite-control iterator, total and polynomial on every raw input. -/
theorem fp_iterate (ec : BitEncoding C) (es : BitEncoding S) (fallback : S)
    (transition : C × S → Option S) (ht : FP (ec.prod es) (optionCode es) transition) :
    FP (BitEncoding.unaryNat.prod (configurationCode ec es)) (configurationCode ec es)
      (fun p => (limitedStep es fallback transition)^[p.1] p.2) := by
  obtain ⟨body⟩ := fp_limitedStep ec es fallback transition ht
  exact ⟨BoundedIterationMachine.computer (configurationCode ec es)
    (limitedStep es fallback transition) body
    (Polynomial.C 3*Polynomial.X + Polynomial.C ((es.encode fallback).length+2))
    (fun count p i _ => iterate_code_bound ec es fallback transition count p i)⟩

/-- On a genuinely bounded candidate no cap branch is taken. -/
theorem limitedStep_eq (es : BitEncoding S) (fallback : S)
    (transition : C × S → Option S) (p : Configuration C S)
    (h : (es.encode (next transition (p.1,p.2.2))).length ≤ p.2.1) :
    limitedStep es fallback transition p = (p.1,p.2.1,next transition (p.1,p.2.2)) := by
  simp only [limitedStep,h,↓reduceIte]

/-- A genuine bounded run agrees exactly with the uncapped control program. -/
theorem iterate_eq_of_bound (es : BitEncoding S) (fallback : S)
    (transition : C × S → Option S) (c : C) (budget : ℕ) (initial : S)
    (count : ℕ)
    (hbound : ∀ i, i ≤ count →
      (es.encode ((fun s => next transition (c,s))^[i] initial)).length ≤ budget) :
    (limitedStep es fallback transition)^[count] (c,budget,initial) =
      (c,budget,(fun s => next transition (c,s))^[count] initial) := by
  induction count with
  | zero => rfl
  | succ count ih =>
    have hi := ih (fun i hi => hbound i (by omega))
    rw [Function.iterate_succ_apply',hi]
    rw [Function.iterate_succ_apply']
    exact limitedStep_eq es fallback transition _ (by
      simpa only [Function.iterate_succ_apply'] using hbound (count+1) le_rfl)

def runWithBudgets (ec : BitEncoding C) (es : BitEncoding S) (fallback : S)
    (transition : C × S → Option S) (space time : Polynomial ℕ) (p : C × S) : S :=
  let N := ((ec.prod es).encode p).length
  ((limitedStep es fallback transition)^[time.eval N] (p.1,space.eval N,p.2)).2.2

/-- Both loop fuel and state cap are computed by actual unary polynomial
machines from the literal input length. The resulting program is FP on all data. -/
theorem fp_runWithBudgets (ec : BitEncoding C) (es : BitEncoding S) (fallback : S)
    (transition : C × S → Option S) (ht : FP (ec.prod es) (optionCode es) transition)
    (space time : Polynomial ℕ) :
    FP (ec.prod es) es (runWithBudgets ec es fallback transition space time) := by
  have hlen : FP (ec.prod es) BitEncoding.unaryNat (fun p => ((ec.prod es).encode p).length) :=
    ⟨InputLengthMachine.computer (ec.prod es)⟩
  have hs := hlen.comp (UnaryPolynomialMachines.fp_eval space)
  have ht' := hlen.comp (UnaryPolynomialMachines.fp_eval time)
  have hi := ht'.pair ((fp_fst ec es).pair (hs.pair (fp_snd ec es)))
  have hr := hi.comp (fp_iterate ec es fallback transition ht)
  exact hr.comp ((fp_snd ec (BitEncoding.unaryNat.prod es)).comp (fp_snd BitEncoding.unaryNat es))

theorem runWithBudgets_correct (ec : BitEncoding C) (es : BitEncoding S) (fallback : S)
    (transition : C × S → Option S) (space time : Polynomial ℕ) (p : C × S)
    (hbound : ∀ i, i ≤ time.eval ((ec.prod es).encode p).length →
      (es.encode ((fun s => next transition (p.1,s))^[i] p.2)).length ≤
        space.eval ((ec.prod es).encode p).length) :
    runWithBudgets ec es fallback transition space time p =
      (fun s => next transition (p.1,s))^[time.eval ((ec.prod es).encode p).length] p.2 := by
  unfold runWithBudgets
  dsimp only
  rw [iterate_eq_of_bound es fallback transition p.1 _ p.2 _ hbound]

end ComplexCSP.ComplexityCappedIteration
