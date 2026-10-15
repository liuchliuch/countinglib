import Paper2.Complexity.BellMachines.ListCombinators

/-! Generic literal list operations for graph editing. Unbounded lists are
processed by actual returning stack loops; no host list function is an opcode. -/
namespace Paper2.Complexity.BellMachines.Lists
open Turing Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open GraphPreprocessing.OriginalCoefficient FixedGadgetSubstitution.Compiler
open Paper2.Complexity.BellMachines.Codecs
open StackProtocol
noncomputable section
variable {A B C : Type}

/-- Contextual filtering retains original order and every retained entry byte. -/
def filterComputes (ea : Encoding A Bool) (eb : Encoding B Bool)
    (p : A → B → Bool)
    (test : Computes (pairEncoding ea eb) encodingBoolBool (fun x => p x.1 x.2)) :
    Computes (pairEncoding ea (framedListEncoding eb)) (framedListEncoding eb)
      (fun x => x.2.filter (p x.1)) := by
  let cell : Computes (pairEncoding ea eb) Frame.wordEncoding
      (fun x => if p x.1 x.2 then entry eb x.2 else []) :=
    ifComputes test ((Wiring.secondComputes ea eb).andThen (entryComputes eb))
      (constantComputes (pairEncoding ea eb) Frame.wordEncoding [])
  let provider : Computes (sigmaEncoding ea (fun _ => eb)) Frame.wordEncoding
      (fun x => if p x.1 x.2 then entry eb x.2 else []) :=
    recode cell (fun x => (x.1, x.2)) (fun _ => rfl) (fun _ => rfl)
  let run : Computes (pairEncoding ea (framedListEncoding eb)) Frame.wordEncoding
      (fun x => x.2.flatMap (fun b => if p x.1 b then entry eb b else [])) :=
    recode (ContextFlatMap.computes ea (fun _ => eb) _ provider)
      (fun x => ⟨x.1, x.2⟩) (fun _ => rfl) (fun _ => rfl)
  apply recode (joinComputes run
    (constantComputes (pairEncoding ea (framedListEncoding eb)) Frame.wordEncoding [false]))
    id (fun _ => rfl)
  intro x
  change (x.2.flatMap (fun b => if p x.1 b then entry eb b else [])) ++ [false] =
    framedListEncode eb (x.2.filter (p x.1))
  induction x.2 with
  | nil => rfl
  | cons b bs ih =>
    cases hp : p x.1 b
    · simpa only [List.flatMap_cons, List.filter_cons, hp, Bool.false_eq_true,
        ite_false, List.nil_append] using ih
    · simp only [List.flatMap_cons, List.filter_cons, hp, ite_true]
      rw [List.append_assoc, ih]
      rfl

/-- Appending two runtime lists scans and physically serializes both operands. -/
def appendListsComputes (e : Encoding B Bool) :
    Computes (pairEncoding (framedListEncoding e) (framedListEncoding e))
      (framedListEncoding e) (fun p => p.1 ++ p.2) := by
  let first := (Wiring.firstComputes (framedListEncoding e) (framedListEncoding e)).andThen
    (entriesComputes e)
  let second := (Wiring.secondComputes (framedListEncoding e) (framedListEncoding e)).andThen
    (encodeComputes (framedListEncoding e))
  exact recode (joinComputes first second) id (fun _ => rfl)
    (fun p => entries_append_encode e p.1 p.2)

/-- A contextual flatMap has a real byte-level loop, including inner framing. -/
def flatMapComputes (ea : Encoding A Bool) (eb : Encoding B Bool) (ec : Encoding C Bool)
    (f : A → B → List C)
    (cell : Computes (pairEncoding ea eb) (framedListEncoding ec) (fun x => f x.1 x.2)) :
    Computes (pairEncoding ea (framedListEncoding eb)) (framedListEncoding ec)
      (fun x => x.2.flatMap (f x.1)) := by
  let provider : Computes (sigmaEncoding ea (fun _ => eb)) Frame.wordEncoding
      (fun x => entries ec (f x.1 x.2)) :=
    recode (cell.andThen (entriesComputes ec)) (fun x => (x.1, x.2))
      (fun _ => rfl) (fun _ => rfl)
  let run : Computes (pairEncoding ea (framedListEncoding eb)) Frame.wordEncoding
      (fun x => x.2.flatMap (fun b => entries ec (f x.1 b))) :=
    recode (ContextFlatMap.computes ea (fun _ => eb) _ provider)
      (fun x => ⟨x.1, x.2⟩) (fun _ => rfl) (fun _ => rfl)
  apply recode (joinComputes run
    (constantComputes (pairEncoding ea (framedListEncoding eb)) Frame.wordEncoding [false]))
    id (fun _ => rfl)
  intro x
  have h := entries_append_encode ec (x.2.flatMap (f x.1)) []
  simpa only [entries, List.flatMap_assoc, List.append_nil, framedListEncode,
    framedListEncoding, Frame.wordEncoding, id_eq] using h

namespace Length

abbrev machine : BinaryCompose.Machine where
  K := Bool
  input := false
  output := true
  Label := Fin 4
  main := 0
  State := Option Bool × Unit
  initial := (none, ())
  program label := if label = 0 then ListScan.markerStmt false true 0 1 2 3
    else if label = 1 then ListScan.skipStmt false 1 0 3 else .halt

theorem run (e : Encoding B Bool) (xs : List B) :
    RunsExactly machine.computer.step
      (initList machine.computer ((framedListEncoding e).encode xs))
      (haltList machine.computer (List.replicate xs.length true)) (ListScan.ticks e xs + 1) := by
  let tapes : Bool → List Bool := fun _ => []
  have h := ListScan.count_exact false true (by decide) machine.computer.step 0 1 2 3
    (executesAt_tm2 _ _ _ rfl) (executesAt_tm2 _ _ _ rfl) e () tapes xs [] []
  have hi : cfg (0 : Fin 4) ()
      (ListScan.tapes2 tapes false true (framedListEncode e xs ++ []) []) =
      initList machine.computer ((framedListEncoding e).encode xs) := by
    rw [Machine.init_eq]
    congr 1
    funext k
    cases k <;> simp [ListScan.tapes2, tapes, wordTape, Function.update, framedListEncoding]
  rw [hi] at h
  have last : machine.computer.step
      (cfg (2 : Fin 4) ()
        (ListScan.tapes2 tapes false true [] (List.replicate xs.length true ++ []))) =
      some (haltList machine.computer (List.replicate xs.length true)) := by
    rw [Machine.halt_eq]
    simp only [machine, FinTM2.step, TM2.step, Fin.isValue, Fin.reduceEq, ite_false,
      cfg, TM2.stepAux]
    congr 2
    funext k
    cases k <;> simp [ListScan.tapes2, tapes, wordTape, Function.update, framedListEncoding]
  simpa only [Nat.add_comm] using h.trans (runsExactly_one last)

end Length

/-- One actual output token per list entry, with a linear transition bound. -/
def lengthUnaryComputes (e : Encoding B Bool) :
    Computes (framedListEncoding e) UnaryBinary.unaryEncoding List.length where
  machine := Length.machine
  time := Polynomial.X + 1
  outputs xs := {
    steps := ListScan.ticks e xs + 1
    evals_in_steps := Length.run e xs
    steps_le_m := by
      have h := ListScan.ticks_le_length e xs
      simpa [framedListEncoding] using Nat.add_le_add_right h 1 }

/-- Binary count is produced by the actual unary-to-binary carry machine. -/
def lengthBinaryComputes (e : Encoding B Bool) :
    Computes (framedListEncoding e) encodingNatBool List.length :=
  (lengthUnaryComputes e).andThen UnaryBinary.computes

end
end Paper2.Complexity.BellMachines.Lists
