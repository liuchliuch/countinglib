import Counting.Algorithm.InterpolationMachine.Materialized.Machine

/-! Runtime rational tables, including a zero node, fractional nodes, cancellation,
empty and singleton tables, and the explicit boundary at repeated nodes. -/
namespace Counting.Algorithm.InterpolationMachine.Materialized.Clients
open Turing PlanarHom.Complexity

noncomputable def rationalBasis : Module.Basis (Fin 1) ℚ ℚ :=
  Module.Basis.singleton (Fin 1) ℚ

def nodes : Fin 3 → ℚ := ![0, 1 / 2, 2]
def samples : Fin 3 → ℚ := ![3, 5 / 2, 7]
def quadratic : Table ℚ := [(0, 3), (1 / 2, 5 / 2), (2, 7)]

theorem nodes_injective : Function.Injective nodes := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | (norm_num [nodes] at h)

theorem quadratic_table : quadratic = tableOf nodes samples := rfl

theorem samples_correct (i : Fin 3) : samples i = 2 * (nodes i)^2 - 2 * nodes i + 3 := by
  fin_cases i <;> norm_num [samples, nodes]

theorem quadratic_recover : recover quadratic = 2 := by
  norm_num [recover, quadratic, rowTerm, denominator, otherNodes]

theorem quadratic_public : Interpolation.evaluate nodes samples = 2 := by
  rw [← recover_eq_evaluate nodes samples nodes_injective, ← quadratic_table]
  exact quadratic_recover

theorem zero_node_denominator : denominator (0, otherNodes (0 : ℚ) quadratic) = 1 := by
  norm_num [denominator, otherNodes, quadratic]

noncomputable def quadratic_machine : TM2OutputsInTime (computer rationalBasis).tm
    (((inputEncoding rationalBasis).encode quadratic).map (computer rationalBasis).inputAlphabet.symm)
    (some (((numberFieldEncoding rationalBasis).encode 2).map (computer rationalBasis).outputAlphabet.symm))
    ((computer rationalBasis).time.eval ((inputEncoding rationalBasis).encode quadratic).length) := by
  simpa only [quadratic_recover] using outputs rationalBasis quadratic

noncomputable def zero_machine (ns : List ℚ) : TM2OutputsInTime (computer rationalBasis).tm
    (((inputEncoding rationalBasis).encode (ns.map (fun x => (x, 0)))).map
      (computer rationalBasis).inputAlphabet.symm)
    (some (((numberFieldEncoding rationalBasis).encode 0).map (computer rationalBasis).outputAlphabet.symm))
    ((computer rationalBasis).time.eval ((inputEncoding rationalBasis).encode
      (ns.map (fun x => (x, 0)))).length) := by
  simpa only [recover_zero] using outputs rationalBasis (ns.map (fun x => (x, 0)))

/-- Degree zero remains valid at node zero for every materialized rational sample. -/
noncomputable def singleton_zero_machine (value : ℚ) : TM2OutputsInTime (computer rationalBasis).tm
    (((inputEncoding rationalBasis).encode [(0, value)]).map (computer rationalBasis).inputAlphabet.symm)
    (some (((numberFieldEncoding rationalBasis).encode value).map
      (computer rationalBasis).outputAlphabet.symm))
    ((computer rationalBasis).time.eval ((inputEncoding rationalBasis).encode [(0, value)]).length) := by
  simpa only [recover_singleton] using outputs rationalBasis [(0, value)]

theorem cancellation : recover ([(0, 7), (2, 7)] : Table ℚ) = 0 := by
  norm_num [recover, rowTerm, denominator, otherNodes]

/-- The total machine does not silently promise to reject repeated keys. -/
theorem duplicate_total : recover ([(0, 2), (0, 3)] : Table ℚ) = 5 := by
  norm_num [recover, rowTerm, denominator, otherNodes]

/-- I1's checked semantic frontend still rejects these same repeated nodes. -/
theorem duplicate_checked : Interpolation.checkedRecover (![0, 0] : Fin 2 → ℚ) ![2, 3] = none :=
  Interpolation.checkedRecover_duplicate _ _ 0 1 (by decide) (by rfl)

end Counting.Algorithm.InterpolationMachine.Materialized.Clients
