/- Extracted concrete finite-machine foundation; see docs/BELL_LIST_MACHINES_REUSE.json. -/
import Paper2.Complexity.BellMachines.GraphPreprocessing.Frame
namespace Paper2.Complexity.BellMachines.BoundedDecode
open Turing Computability Paper2.Complexity StackProtocol Turing.TM2.Stmt
variable {A K Λ τ : Type} [DecidableEq K]
/-- A bounded, statically unrolled decoder. EOF invokes the compile-time leaf;
extra bits after the bound go to `bad`. Its only register is `Option Bool`. -/
def decodeStmt (src : K) (leaf : List Bool → Λ) (bad : Λ) :
    ℕ → List Bool → Stmt K Λ τ
  | 0, pre =>
      pop src (fun v b => (b, v.2)) (branch (fun v => v.1.isSome)
        (load (fun v => (none, v.2)) (goto (fun _ => bad)))
        (load (fun v => (none, v.2)) (goto (fun _ => leaf pre))))
  | fuel + 1, pre =>
      pop src (fun v b => (b, v.2)) (branch (fun v => v.1.isSome)
        (branch (fun v => v.1.getD false)
          (decodeStmt src leaf bad fuel (pre ++ [true]))
          (decodeStmt src leaf bad fuel (pre ++ [false])))
        (load (fun v => (none, v.2)) (goto (fun _ => leaf pre))))

/-- The decision tree acts entirely through actual pop/branch/load/goto syntax. -/
theorem decodeStmt_exact (src : K) (leaf : List Bool → Λ) (bad : Λ)
    (fuel : ℕ) (pre word : List Bool) (h : word.length ≤ fuel)
    (v : Option Bool × τ) (tapes : K → List Bool) :
    TM2.stepAux (decodeStmt src leaf bad fuel pre) v
        (Function.update tapes src word) =
      cfg (leaf (pre ++ word)) v.2 (Function.update tapes src []) := by
  induction fuel generalizing pre word v with
  | zero =>
    have hw : word = [] := List.length_eq_zero_iff.mp (by omega)
    subst word
    simp [decodeStmt, TM2.stepAux, cfg]
  | succ fuel ih =>
    cases word with
    | nil => simp [decodeStmt, TM2.stepAux, cfg]
    | cons bit word =>
      have hw : word.length ≤ fuel := by simp only [List.length_cons] at h; omega
      cases bit with
      | false =>
        simpa [decodeStmt, TM2.stepAux, List.append_assoc, Function.update_idem] using
          ih (pre ++ [false]) word hw (some false, v.2)
      | true =>
        simpa [decodeStmt, TM2.stepAux, List.append_assoc, Function.update_idem] using
          ih (pre ++ [true]) word hw (some true, v.2)

omit [DecidableEq K] in
/-- Even the nested decision tree has a linear per-transition primitive budget. -/
theorem decodeStmt_budget (src : K) (leaf : List Bool → Λ) (bad : Λ)
    (fuel : ℕ) (pre : List Bool) :
    TM2Cost.budget (decodeStmt (τ := τ) src leaf bad fuel pre) ≤ 3 * fuel + 4 := by
  induction fuel generalizing pre with
  | zero => rfl
  | succ fuel ih =>
    simp only [decodeStmt, TM2Cost.budget]
    have ht := ih (pre ++ [true])
    have hf := ih (pre ++ [false])
    omega


end Paper2.Complexity.BellMachines.BoundedDecode
