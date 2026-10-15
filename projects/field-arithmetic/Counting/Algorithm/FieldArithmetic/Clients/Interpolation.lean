import Counting.Algorithm.InterpolationMachine.Materialized.Semantics
import Counting.Algorithm.FieldArithmetic.Materialized
import PlanarHom.ListContextFilterMachines
import PlanarHom.FiniteReachableAlphabetMachines
import Holant.Complexity.Encoding

/-! Reconstruct the accepted materialized interpolation client through the new
public arithmetic entry. The canonical runtime-table semantics are shared.
A fixed number field, but runtime nodes, samples and table length.
Every map/filter/fold and arithmetic operation below invokes an actual compiled
TM2. No polynomial-time evaluator is supplied by the caller. -/
namespace Counting.Algorithm.FieldArithmetic.Clients.Interpolation
open Counting.Algorithm.InterpolationMachine.Materialized
open PlanarHom PlanarHom.Complexity PlanarHom.ArithmeticCircuitPrimitives
open PlanarHom.Complexity.PairProjectionMachines Turing
noncomputable section
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

noncomputable def inputEncoding : BitEncoding (Table K) :=
  ((numberFieldEncoding basis).prod (numberFieldEncoding basis)).list

theorem fp_otherNodes : FP ((numberFieldEncoding basis).prod (inputEncoding basis))
    (numberFieldEncoding basis).list (fun p => otherNodes p.1 p.2) := by
  have hm := fp_fst (numberFieldEncoding basis) (inputEncoding basis)
  have ht := fp_snd (numberFieldEncoding basis) (inputEncoding basis)
  have hn := ht.comp (ListMapMachines.fp_map _ _ Prod.fst
    (fp_fst (numberFieldEncoding basis) (numberFieldEncoding basis)))
  have hneq : FP ((numberFieldEncoding basis).prod (numberFieldEncoding basis)) BitEncoding.bool
      (fun p : K × K => decide (p.2 ≠ p.1)) :=
    ((FieldArithmetic.fp_equality basis).comp (fp_bool_unary BitEncoding.bool not)).congr
      (fun p => by simp [eq_comm])
  exact (hm.pair hn).comp (ListContextFilterMachines.fp_filterWithContext _ _ _ hneq)

omit [DecidableEq K] in
/-- Difference-map followed by the materialized product machine, without the
extra node multiplication in the source's shifted denominator. -/
theorem fp_denominator : FP ((numberFieldEncoding basis).prod (numberFieldEncoding basis).list)
    (numberFieldEncoding basis) (denominator : K × List K → K) := by
  have hd := ListContextMachines.fp_mapWithContext (numberFieldEncoding basis)
    (numberFieldEncoding basis) (numberFieldEncoding basis)
    (fun p : K × K => p.1 - p.2) (FieldArithmetic.fp_subtraction basis)
  exact hd.comp (FieldArithmetic.Materialized.fp_product basis)

theorem fp_rowTerm : FP ((inputEncoding basis).prod
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis)))
    (numberFieldEncoding basis) (fun p => rowTerm p.1 p.2) := by
  have ht := fp_fst (inputEncoding basis)
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis))
  have hr := fp_snd (inputEncoding basis)
    ((numberFieldEncoding basis).prod (numberFieldEncoding basis))
  have hn := hr.comp (fp_fst (numberFieldEncoding basis) (numberFieldEncoding basis))
  have hv := hr.comp (fp_snd (numberFieldEncoding basis) (numberFieldEncoding basis))
  have ho := (hn.pair ht).comp (fp_otherNodes basis)
  have hd := (hn.pair ho).comp (fp_denominator basis)
  exact (hv.pair hd).comp (FieldArithmetic.fp_division basis)

theorem fp_rows : FP (inputEncoding basis) (numberFieldEncoding basis).list
    (fun table => table.map (rowTerm table)) :=
  ((fp_id (inputEncoding basis)).pair (fp_id (inputEncoding basis))).comp
    (ListContextMachines.fp_mapWithContext (inputEncoding basis)
      ((numberFieldEncoding basis).prod (numberFieldEncoding basis)) (numberFieldEncoding basis)
      (fun p => rowTerm p.1 p.2) (fp_rowTerm basis))

/-- Total FP for every materialized table, measured in its exact serialized bit
length. Distinctness is required only by the semantic interpolation theorem. -/
theorem fp_recover : FP (inputEncoding basis) (numberFieldEncoding basis) (recover : Table K → K) :=
  (fp_rows basis).comp (FieldArithmetic.Materialized.fp_sum basis)

omit [DecidableEq K] in
/-- Every accumulator of the actual denominator's product fold has polynomial
canonical bit length in its serialized node/list input, without a height promise. -/
theorem denominator_prefix_bound : ∃ p : Polynomial ℕ, ∀ (node : K) (xs : List K) (i : ℕ),
    ((numberFieldEncoding basis).encode
      (((xs.map (fun x => node - x)).take i).prod)).length ≤
      p.eval (((numberFieldEncoding basis).prod (numberFieldEncoding basis).list).encode
        (node, xs)).length := by
  let e := numberFieldEncoding basis
  let ein := e.prod e.list
  have hd := ListContextMachines.fp_mapWithContext e e e
    (fun p : K × K => p.1 - p.2) (FieldArithmetic.fp_subtraction basis)
  obtain ⟨prepare⟩ := (fp_const ein e 1).pair hd
  obtain ⟨p, hp⟩ := FieldArithmetic.Materialized.exists_polynomial_prefix_encoding_bound basis
  refine ⟨p.comp (MachineComposition.outputLengthPolynomial prepare), ?_⟩
  intro node xs i
  have hb := (hp 1 (xs.map (fun x => node - x)) i).1
  simp only [one_mul] at hb
  exact hb.trans (by
    rw [Polynomial.eval_comp]
    exact MachineComposition.natPolynomial_monotone p
      (MachineComposition.encoded_output_length_le prepare (node, xs)))

/-- Every accumulator in the final sum is charged to the whole runtime table.
The row-list computer's actual output bound pays for all materialized quotients. -/
theorem sum_prefix_bound : ∃ p : Polynomial ℕ, ∀ (table : Table K) (i : ℕ),
    ((numberFieldEncoding basis).encode ((table.map (rowTerm table)).take i).sum).length ≤
      p.eval ((inputEncoding basis).encode table).length := by
  obtain ⟨prepare⟩ := (fp_const (inputEncoding basis) (numberFieldEncoding basis) 0).pair
    (fp_rows basis)
  obtain ⟨p, hp⟩ := FieldArithmetic.Materialized.exists_polynomial_prefix_encoding_bound basis
  refine ⟨p.comp (MachineComposition.outputLengthPolynomial prepare), ?_⟩
  intro table i
  have hb := (hp 0 (table.map (rowTerm table)) i).2
  simp only [zero_add] at hb
  exact hb.trans (by
    rw [Polynomial.eval_comp]
    exact MachineComposition.natPolynomial_monotone p
      (MachineComposition.encoded_output_length_le prepare table))

noncomputable def sourceComputer : TM2ComputableInPolyTime
    (inputEncoding basis).encode (numberFieldEncoding basis).encode (recover : Table K → K) :=
  Classical.choice (fp_recover basis)

/-- The canonical reachable-symbol compiler supplies finite alphabets for all
stacks, retaining the very same input/output words, time and transition count. -/
noncomputable def computer : Holant.Complexity.PolyTime
    (inputEncoding basis).toFinEncoding (numberFieldEncoding basis).toFinEncoding
    (recover : Table K → K) where
  toTM2ComputableInPolyTime := FiniteReachableAlphabetMachines.restrictComputer (sourceComputer basis)
  finiteAlphabets := FiniteReachableAlphabetMachines.alphabetFintype (sourceComputer basis)

theorem inFP : Holant.Complexity.InFP
    (inputEncoding basis).toFinEncoding (numberFieldEncoding basis).toFinEncoding
    (recover : Table K → K) := ⟨computer basis⟩

@[simp] theorem computer_time : (computer basis).time = (sourceComputer basis).time := rfl

@[simp] theorem computer_steps (table : Table K) :
    ((computer basis).outputsFun table).steps = ((sourceComputer basis).outputsFun table).steps := rfl

def outputs (table : Table K) : TM2OutputsInTime (computer basis).tm
    (((inputEncoding basis).encode table).map (computer basis).inputAlphabet.symm)
    (some (((numberFieldEncoding basis).encode (recover table)).map (computer basis).outputAlphabet.symm))
    ((computer basis).time.eval ((inputEncoding basis).encode table).length) :=
  (computer basis).outputsFun table

def outputs_evaluate {m : ℕ} (nodes values : Fin (m + 1) → K)
    (hi : Function.Injective nodes) : TM2OutputsInTime (computer basis).tm
    (((inputEncoding basis).encode (tableOf nodes values)).map (computer basis).inputAlphabet.symm)
    (some (((numberFieldEncoding basis).encode (Counting.Algorithm.Interpolation.evaluate nodes values)).map
      (computer basis).outputAlphabet.symm))
    ((computer basis).time.eval ((inputEncoding basis).encode (tableOf nodes values)).length) := by
  simpa only [recover_eq_evaluate nodes values hi] using outputs basis (tableOf nodes values)

def outputs_coefficient {m : ℕ} (nodes : Fin (m + 1) → K)
    (hi : Function.Injective nodes) (P : Polynomial K) (hP : P.natDegree ≤ m) :
    TM2OutputsInTime (computer basis).tm
      (((inputEncoding basis).encode (tableOf nodes (fun i => P.eval (nodes i)))).map
        (computer basis).inputAlphabet.symm)
      (some (((numberFieldEncoding basis).encode (P.coeff m)).map (computer basis).outputAlphabet.symm))
      ((computer basis).time.eval ((inputEncoding basis).encode
        (tableOf nodes (fun i => P.eval (nodes i)))).length) := by
  simpa only [recover_eq_coefficient nodes hi P hP] using
    outputs basis (tableOf nodes (fun i => P.eval (nodes i)))

/-- A polynomial extracted from the actual finite program's push bound and
proved time controls every stack at every intermediate reached configuration. -/
noncomputable def stackBound : Polynomial ℕ :=
  MachineComposition.outputLengthPolynomial (computer basis).toTM2ComputableInPolyTime

theorem intermediate_stack_bound (table : Table K) (t : ℕ)
    (c : (computer basis).tm.Cfg)
    (hrun : ((fun q : Option (computer basis).tm.Cfg => q.bind (computer basis).tm.step)^[t])
      (some (Turing.initList (computer basis).tm
        (((inputEncoding basis).encode table).map (computer basis).inputAlphabet.symm))) = some c)
    (ht : t ≤ ((computer basis).outputsFun table).steps) (k : (computer basis).tm.K) :
    (c.stk k).length ≤ (stackBound basis).eval ((inputEncoding basis).encode table).length := by
  let tm := (computer basis).tm
  let xs := ((inputEncoding basis).encode table).map (computer basis).inputAlphabet.symm
  have hinit : ∀ j, ((Turing.initList tm xs).stk j).length ≤ xs.length := by
    intro j
    rw [MachineComposition.initList_stk]
    by_cases hj : j = tm.k₀
    · subst j
      simp [MachineComposition.pointStack]
    · simp [MachineComposition.pointStack, hj]
  have hb := MachineComposition.iterate_length_le tm (Turing.initList tm xs) c t xs.length
    hrun hinit k
  have htime := ht.trans ((computer basis).outputsFun table).steps_le_m
  calc
    (c.stk k).length ≤ xs.length + t * MachineComposition.machinePushBound tm := hb
    _ ≤ xs.length + (computer basis).time.eval ((inputEncoding basis).encode table).length *
        MachineComposition.machinePushBound tm := Nat.add_le_add_left (Nat.mul_le_mul_right _ htime) _
    _ = (stackBound basis).eval ((inputEncoding basis).encode table).length := by
      simp [stackBound, MachineComposition.outputLengthPolynomial, xs, tm, Nat.mul_comm]

end
end Counting.Algorithm.FieldArithmetic.Clients.Interpolation
