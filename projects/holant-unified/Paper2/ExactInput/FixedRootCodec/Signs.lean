import Paper2.Complexity.BellMachines.RationalArithmetic.ScalarMachines
import Paper2.Complexity.StackProtocol
import Paper2.Complexity.BellMachines.GraphPreprocessing.Frame

/-! Exact sign tests needed by fixed-polynomial root bisection. The integer
sign is the parity bit of the established canonical codec. The finite machine
reads that bit and erases the rest of the input before returning one Boolean.
All erasing transitions are included in its polynomial bound. -/
namespace Paper2.ExactInput.FixedRootCodec
open Turing Computability Paper2.Complexity Paper2.Complexity.BinaryCompose
open StackProtocol Paper2.Complexity.FixedFieldMachines
open Turing.TM2.Stmt
noncomputable section

abbrev headMachine : Machine where
  K := Bool
  input := false
  output := true
  Label := Bool
  main := false
  State := Option Bool × Bool
  initial := (none,false)
  program label := if !label then
    pop false (fun _ b => (none,b.getD false)) (goto (fun _ => true))
  else
    pop false (fun v b => (b,v.2))
      (branch (fun v => v.1.isSome)
        (load (fun v => (none,v.2)) (goto (fun _ => true)))
        (push true (fun v => v.2) (load (fun _ => (none,false)) .halt)))

def headTapes (word : List Bool) : Bool → List Bool :=
  fun k => if k then [] else word

def headConfig (word : List Bool) (bit : Bool) : headMachine.Config :=
  ⟨some true,(none,bit),headTapes word⟩

theorem head_first (word : List Bool) :
    headMachine.computer.step (initList headMachine.computer word) =
      some (headConfig word.tail (word.head?.getD false)) := by
  rw [Machine.init_eq]
  cases word with
  | nil =>
    change some (⟨some true,(none,false),Function.update (wordTape false []) false []⟩ :
      headMachine.Config) = _
    congr 2
    funext k
    cases k <;> simp [headTapes,wordTape,Function.update]
  | cons b bs =>
    change some (⟨some true,(none,b),Function.update (wordTape false (b :: bs)) false bs⟩ :
      headMachine.Config) = _
    congr 2
    funext k
    cases k <;> simp [headTapes,wordTape,Function.update]

theorem head_cons (b bit : Bool) (word : List Bool) :
    headMachine.computer.step (headConfig (b :: word) bit) =
      some (headConfig word bit) := by
  change some (⟨some true,(none,bit),Function.update (headTapes (b :: word)) false word⟩ :
    headMachine.Config) = _
  congr 2
  funext k
  cases k <;> rfl

theorem head_nil (bit : Bool) :
    headMachine.computer.step (headConfig [] bit) =
      some (haltList headMachine.computer [bit]) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,false),Function.update
    (Function.update (headTapes []) false []) true [bit]⟩ : headMachine.Config) = _
  congr 2
  funext k
  cases k <;> simp [wordTape,Function.update]

theorem head_clear (word : List Bool) (bit : Bool) :
    RunsExactly headMachine.computer.step (headConfig word bit)
      (haltList headMachine.computer [bit]) (word.length + 1) := by
  induction word with
  | nil => simpa using runsExactly_one (head_nil bit)
  | cons b bs ih =>
    simpa only [List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
      (runsExactly_one (head_cons b bit bs)).trans ih

def headComputes : Computes (encodingList Bool) encodingBoolBool
    (fun word => word.head?.getD false) where
  machine := headMachine
  time := Polynomial.X + 2
  outputs word := {
    steps := 1 + (word.tail.length + 1)
    evals_in_steps := by
      change RunsExactly headMachine.computer.step (initList headMachine.computer word)
        (haltList headMachine.computer [word.head?.getD false]) (1 + (word.tail.length + 1))
      simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (runsExactly_one (head_first word)).trans
          (head_clear word.tail (word.head?.getD false))
    steps_le_m := by
      simp only [Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_ofNat,encodingList,id_eq]
      cases word <;> simp <;> omega }

/-- Canonical integer sign is obtained from the same actual word scanner. -/
def negativeComputes : Computes IntegerArithmetic.encoding encodingBoolBool
    IntegerArithmetic.negative :=
  recode headComputes IntegerArithmetic.encoding.encode (fun _ => rfl)
    (fun z => congrArg encodingBoolBool.encode (IntegerArithmetic.encoding_head z))

def rationalNegativeComputes : Computes Paper2.Algebraic.rationalEncoding encodingBoolBool
    (fun q => decide (q < 0)) := by
  apply congrComputes (RationalArithmetic.numeratorComputes.andThen negativeComputes)
  intro q
  change IntegerArithmetic.negative q.num = decide (q < 0)
  have h : IntegerArithmetic.negative q.num = decide (q.num < 0) := by
    cases q.num <;> simp [IntegerArithmetic.negative]
  rw [h]
  simp only [decide_eq_decide]
  exact Rat.num_neg

end
end Paper2.ExactInput.FixedRootCodec
