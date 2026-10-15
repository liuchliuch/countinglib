import Paper2.Complexity.BellMachines.ListOperations

/-! Unary predecessor and fixed-element list emission by literal stack loops.
The fixed element's frame is part of finite program syntax, not a runtime word
opcode. Each input marker creates precisely one serialized output entry. -/
namespace Paper2.Complexity.BellMachines.UnaryList
open Turing Computability BinaryCompose StackProtocol FixedFieldMachines GraphPreprocessing
open Turing.TM2.Stmt

abbrev predMachine : Machine where
  K := Unit
  input := ()
  output := ()
  Label := Unit
  main := ()
  State := Unit
  initial := ()
  program _ := pop () (fun _ _ => ()) .halt

noncomputable def predecessor : Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding
    (fun n => n-1) where
  machine := predMachine
  time := 1
  outputs n := {
    steps := 1
    evals_in_steps := by
      change predMachine.computer.step (initList predMachine.computer (List.replicate n true)) =
        some (haltList predMachine.computer (List.replicate (n-1) true))
      rw [Machine.init_eq,Machine.halt_eq]
      change predMachine.computer.step ⟨some (),(),wordTape () (List.replicate n true)⟩ = _
      cases n <;> rfl
    steps_le_m := by simp }

abbrev machine (word : List Bool) : Machine where
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
        (Constant.pushWord true word (load (fun _ => (none,())) (goto (fun _ => true))))
        (load (fun _ => (none,())) .halt))
    else push true (fun _ => false) (goto (fun _ => true))

def tapes (input output : List Bool) : Bool → List Bool := fun b => if b then output else input

 theorem step_cons (word : List Bool) (input output : List Bool) :
    (machine word).computer.step (cfg true () (tapes (true::input) output)) =
      some (cfg true () (tapes input (word++output))) := by
  change some (TM2.stepAux (Constant.pushWord true word
    (load (fun _ => (none,())) (goto (fun _ => true)))) (some true,())
      (Function.update (tapes (true::input) output) false input)) = _
  rw [Constant.pushWord_eval]
  dsimp only [TM2.stepAux,cfg]
  congr 2
  funext b; cases b <;> simp [tapes,Function.update,TM2.stepAux,cfg]

 theorem step_nil (word output : List Bool) :
    (machine word).computer.step (cfg true () (tapes [] output)) =
      some (haltList (machine word).computer output) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,()),Function.update (tapes [] output) false []⟩ : (machine word).Config) = _
  congr 2
  funext b; cases b <;> simp [tapes,wordTape,Function.update]

 theorem run {A : Type} (e : Encoding A Bool) (a : A) (n k : ℕ) :
    RunsExactly (machine (FixedGadgetSubstitution.Compiler.entry e a)).computer.step
      (cfg true () (tapes (List.replicate n true) (framedListEncode e (List.replicate k a))))
      (haltList (machine (FixedGadgetSubstitution.Compiler.entry e a)).computer
        (framedListEncode e (List.replicate (n+k) a))) (n+1) := by
  induction n generalizing k with
  | zero => simpa only [List.replicate_zero,Nat.zero_add] using
      runsExactly_one (step_nil _ (framedListEncode e (List.replicate k a)))
  | succ n ih =>
    have h := (runsExactly_one (step_cons (FixedGadgetSubstitution.Compiler.entry e a)
      (List.replicate n true) (framedListEncode e (List.replicate k a)))).trans (ih (k+1))
    simpa only [List.replicate_succ,framedListEncode,FixedGadgetSubstitution.Compiler.entry,
      List.cons_append,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

noncomputable def replicateComputes {A : Type} (e : Encoding A Bool) (a : A) :
    Computes UnaryBinary.unaryEncoding (framedListEncoding e) (fun n => List.replicate n a) where
  machine := machine (FixedGadgetSubstitution.Compiler.entry e a)
  time := Polynomial.X+2
  outputs n := {
    steps := (n+1)+1
    evals_in_steps := by
      have first : (machine (FixedGadgetSubstitution.Compiler.entry e a)).computer.step
          (initList (machine (FixedGadgetSubstitution.Compiler.entry e a)).computer (List.replicate n true)) =
          some (cfg true () (tapes (List.replicate n true) [false])) := by
        rw [Machine.init_eq]
        change some (cfg true () (Function.update (wordTape false (List.replicate n true)) true [false])) = _
        congr 2
        funext b; cases b <;> simp [tapes,wordTape,Function.update]
      have h := (runsExactly_one first).trans (run e a n 0)
      change RunsExactly _ _ _ _
      simpa only [List.replicate_zero,framedListEncode,Nat.add_zero,
        UnaryBinary.unaryEncoding,framedListEncoding] using h
    steps_le_m := by simp [UnaryBinary.unaryEncoding] }

end Paper2.Complexity.BellMachines.UnaryList
