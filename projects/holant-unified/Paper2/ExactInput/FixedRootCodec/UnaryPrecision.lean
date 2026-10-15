import Paper2.ExactInput.FixedRootCodec.Signs
import Paper2.Complexity.BellMachines.GraphPreprocessing.UnaryBinary
import Paper2.Complexity.BellMachines.FixedFieldMachines.Constant

/-! A real word scanner emits an affine unary precision counter. Every input
bit is consumed by a returning transition; the multiplier and offset are fixed
finite instruction syntax. There is no host input-length instruction. -/
namespace Paper2.ExactInput.FixedRootCodec
open Turing Computability Paper2.Complexity BinaryCompose StackProtocol FixedFieldMachines
open GraphPreprocessing Turing.TM2.Stmt
noncomputable section

abbrev precisionMachine (A C : ℕ) : Machine where
  K := Bool
  input := false
  output := true
  Label := Bool
  main := false
  State := Option Bool × Unit
  initial := (none,())
  program phase := if phase then
    pop false (fun _ b => (b,()))
      (branch (fun v => v.1.isSome)
        (Constant.pushWord true (List.replicate A true)
          (load (fun _ => (none,())) (goto (fun _ => true))))
        (load (fun _ => (none,())) .halt))
    else Constant.pushWord true (List.replicate C true) (goto (fun _ => true))

def precisionTapes (word output : List Bool) : Bool → List Bool :=
  fun k => if k then output else word

theorem precision_cons (A C : ℕ) (b : Bool) (word output : List Bool) :
    (precisionMachine A C).computer.step (cfg true () (precisionTapes (b::word) output)) =
      some (cfg true () (precisionTapes word (List.replicate A true ++ output))) := by
  change some (TM2.stepAux (Constant.pushWord true (List.replicate A true)
    (load (fun _ => (none,())) (goto (fun _ => true)))) (some b,())
      (Function.update (precisionTapes (b::word) output) false word)) = _
  rw [Constant.pushWord_eval]
  dsimp only [TM2.stepAux,cfg]
  congr 2
  funext k
  cases k <;> simp [precisionTapes,Function.update,TM2.stepAux,cfg]

theorem precision_nil (A C : ℕ) (output : List Bool) :
    (precisionMachine A C).computer.step (cfg true () (precisionTapes [] output)) =
      some (haltList (precisionMachine A C).computer output) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,()),Function.update (precisionTapes [] output) false []⟩ :
    (precisionMachine A C).Config) = _
  congr 2
  funext k
  cases k <;> simp [precisionTapes,wordTape,Function.update]

theorem precision_run (A C : ℕ) (word : List Bool) (k : ℕ) :
    RunsExactly (precisionMachine A C).computer.step
      (cfg true () (precisionTapes word (List.replicate k true)))
      (haltList (precisionMachine A C).computer (List.replicate (A * word.length + k) true))
      (word.length+1) := by
  induction word generalizing k with
  | nil => simpa using runsExactly_one (precision_nil A C (List.replicate k true))
  | cons b bs ih =>
    have second := ih (A+k)
    rw [List.replicate_add] at second
    have h := (runsExactly_one (precision_cons A C b bs (List.replicate k true))).trans
      second
    simpa only [List.replicate_add,List.length_cons,Nat.mul_add,Nat.mul_one,
      Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

def precisionComputes {α : Type} (e : Encoding α Bool) (A C : ℕ) :
    Computes e UnaryBinary.unaryEncoding (fun x => A * (e.encode x).length + C) where
  machine := precisionMachine A C
  time := Polynomial.X+2
  outputs x := {
    steps := (e.encode x).length+2
    evals_in_steps := by
      have first : (precisionMachine A C).computer.step
          (initList (precisionMachine A C).computer (e.encode x)) =
          some (cfg true () (precisionTapes (e.encode x) (List.replicate C true))) := by
        rw [Machine.init_eq]
        change some (TM2.stepAux (Constant.pushWord true (List.replicate C true)
          (goto (fun _ => true))) (none,()) (wordTape false (e.encode x))) = _
        rw [Constant.pushWord_eval]
        dsimp only [TM2.stepAux,cfg]
        congr 2
        funext k
        cases k <;> simp [precisionTapes,wordTape,Function.update]
      change RunsExactly _ _ _ _
      have h := (runsExactly_one first).trans (precision_run A C (e.encode x) C)
      rw [show (e.encode x).length+1+1 = (e.encode x).length+2 by omega] at h
      exact h
    steps_le_m := by simp }

end
end Paper2.ExactInput.FixedRootCodec
