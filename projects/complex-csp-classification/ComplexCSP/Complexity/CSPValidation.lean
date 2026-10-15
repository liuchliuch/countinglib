import ComplexCSP.Complexity.CSPCode
import ComplexCSP.Complexity.FiniteLookup
import PlanarHom.ListContextMachines
import PlanarHom.UnaryNatConversionMachine

/-! # Real FP validation of raw arbitrary-arity CSP codes

Every label, scope length and occurrence index is checked by actual binary
comparison/list machines. No promise-decider or validation oracle is assumed.
-/
namespace ComplexCSP.ComplexityCSPValidation
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityCSPCode

 theorem fold_and (z : Bool) (xs : List Bool) :
    xs.foldl (fun a b => a && b) z = (z && xs.all id) := by
  induction xs generalizing z with
  | nil => simp
  | cons x xs ih => simp [ih,Bool.and_assoc]

 theorem fp_all : FP BitEncoding.bool.list BitEncoding.bool (fun xs : List Bool => xs.all id) := by
  have hf := ListFoldMachines.fp_foldl BitEncoding.bool BitEncoding.bool (fun a b => a && b)
    (ArithmeticCircuitPrimitives.fp_bool_gate (fun p => p.1 && p.2)) (Polynomial.C 1)
    (by intros; simp [BitEncoding.bool])
  exact (((fp_const BitEncoding.bool.list BitEncoding.bool true).pair
    (fp_id BitEncoding.bool.list)).comp hf).congr (fun xs => by simp [fold_and])

/-- Dynamic list bounds, preserving every repeated position. -/
def allBounded (p : ℕ × List ℕ) : Bool := p.2.all (fun v => decide (v < p.1))

 theorem fp_allBounded : FP (BitEncoding.nat.prod BitEncoding.nat.list) BitEncoding.bool allBounded := by
  have hcmp := ((fp_snd BitEncoding.nat BitEncoding.nat).pair
    (fp_fst BitEncoding.nat BitEncoding.nat)).comp BinaryArithmetic.fp_comparison
  have hm := ListContextMachines.fp_mapWithContext BitEncoding.nat BitEncoding.nat BitEncoding.bool
    (fun p : ℕ × ℕ => decide (p.2 < p.1)) hcmp
  exact (hm.comp fp_all).congr (fun p => by simp [allBounded])

variable {D K : Type} {s : ℕ} (L : Language D K (Fin s))

def arityTable : List (ℕ × ℕ) := List.ofFn (fun i : Fin s => (i.val,L.arity i))
def arityLookup (symbol : ℕ) : ℕ := ComplexityFiniteLookup.lookup 0 (arityTable L) symbol

def constraintValidTest (p : ℕ × (ℕ × List ℕ)) : Bool :=
  decide (p.2.1 < s) && decide (p.2.2.length = arityLookup L p.2.1) && allBounded (p.1,p.2.2)

@[simp] theorem constraintValidTest_correct (n : ℕ) (c : ℕ × List ℕ) :
    constraintValidTest L (n,c) = true ↔ ConstraintValid L n c := by
  by_cases hc : c.1 < s
  · have ha := ComplexityFiniteLookup.lookup_fin_table 0 L.arity (⟨c.1,hc⟩ : Fin s)
    change arityLookup L c.1 = L.arity ⟨c.1,hc⟩ at ha
    simp [constraintValidTest,hc,ha,allBounded,List.all_eq_true,ConstraintValid]
  · simp [constraintValidTest,hc,ConstraintValid]

/-- Actual FP parser for a unary variable bound and binary symbol/scope row. -/
theorem fp_constraintValidTest :
    FP (BitEncoding.unaryNat.prod constraintEncoding) BitEncoding.bool (constraintValidTest L) := by
  let e := BitEncoding.unaryNat.prod constraintEncoding
  have hn := (fp_fst BitEncoding.unaryNat constraintEncoding).comp UnaryNatConversionMachine.fp_conversion
  have hr := fp_snd BitEncoding.unaryNat constraintEncoding
  have hi := hr.comp (fp_fst BitEncoding.nat BitEncoding.nat.list)
  have hv := hr.comp (fp_snd BitEncoding.nat BitEncoding.nat.list)
  have hs := (hi.pair (fp_const e BitEncoding.nat s)).comp BinaryArithmetic.fp_comparison
  have ha := hi.comp (ComplexityFiniteLookup.fp_lookup BitEncoding.nat 0 (arityTable L))
  have hl := hv.comp (Complexity.ListCodecMachines.fp_length BitEncoding.nat)
  have he := (hl.pair ha).comp NatListSumMachines.fp_equal
  have hb := (hn.pair hv).comp fp_allBounded
  exact (((hs.pair he).comp (ArithmeticCircuitPrimitives.fp_bool_gate (fun p => p.1 && p.2))).pair hb).comp
    (ArithmeticCircuitPrimitives.fp_bool_gate (fun p => p.1 && p.2))

/-- Literal whole-instance well-formedness test. -/
def validTest (g : Code) : Bool := g.constraints.all (fun c => constraintValidTest L (g.vertices,c))

@[simp] theorem validTest_correct (g : Code) : validTest L g = true ↔ Valid L g := by
  simp [validTest,List.all_eq_true,Valid]

/-- Total validation is itself a proved bit-machine FP computation. -/
theorem fp_validTest : FP encoding BitEncoding.bool (validTest L) := by
  have hv : FP encoding (BitEncoding.unaryNat.prod constraintEncoding.list)
      (fun g => (g.vertices,g.constraints)) := fp_code_view _ _ _ (fun _ => rfl)
  have hm := ListContextMachines.fp_mapWithContext BitEncoding.unaryNat constraintEncoding BitEncoding.bool
    (constraintValidTest L) (fp_constraintValidTest L)
  exact (hv.comp (hm.comp fp_all)).congr (fun g => by simp [validTest])

end ComplexCSP.ComplexityCSPValidation
