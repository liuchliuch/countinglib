import Paper2.Complexity.BellMachines.RawTripleCompile

/-! Count the actual number of 3-to-1 occurrence surgeries. The finite scanner
removes the first unary marker, then consumes two markers per output marker.
Its output is (count-1)/2, with every pop and EOF test charged. -/
namespace Paper2.Complexity.BellMachines.UnaryRounds
open Turing Computability BinaryCompose StackProtocol FixedFieldMachines GraphPreprocessing
open Turing.TM2.Stmt

abbrev machine : Machine where
  K := Bool
  input := false
  output := true
  Label := Fin 3
  main := 0
  State := Option Bool × Unit
  initial := (none,())
  program i := if i = 0 then
      pop false (fun _ _ => (none,())) (goto (fun _ => 1))
    else if i = 1 then
      pop false (fun _ b => (b,()))
        (branch (fun v => v.1.isSome)
          (load (fun _ => (none,())) (goto (fun _ => 2)))
          (load (fun _ => (none,())) .halt))
    else
      pop false (fun _ b => (b,()))
        (branch (fun v => v.1.isSome)
          (push true (fun _ => true) (load (fun _ => (none,())) (goto (fun _ => 1))))
          (load (fun _ => (none,())) .halt))

def tapes (input output : List Bool) : Bool → List Bool := fun b => if b then output else input
def state (i : Fin 3) (n k : ℕ) := cfg i () (tapes (List.replicate n true) (List.replicate k true))

 theorem first (n : ℕ) : machine.computer.step (initList machine.computer (List.replicate n true)) =
    some (state 1 (n-1) 0) := by
  rw [Machine.init_eq]
  cases n with
  | zero =>
    change some (cfg (1 : Fin 3) () (Function.update (wordTape false []) false [])) = _
    congr 2
    funext b; cases b <;> simp [state,tapes,wordTape,Function.update]
  | succ n =>
    change some (cfg (1 : Fin 3) () (Function.update (wordTape false (List.replicate (n+1) true))
      false (List.replicate n true))) = _
    congr 2
    funext b; cases b <;> simp [state,tapes,wordTape,Function.update]

 theorem pair_first (n k : ℕ) : machine.computer.step (state 1 (n+2) k) =
    some (state 2 (n+1) k) := by
  change some (cfg (2 : Fin 3) () (Function.update
    (tapes (List.replicate (n+2) true) (List.replicate k true)) false (List.replicate (n+1) true))) = _
  congr 2
  funext b; cases b <;> rfl

 theorem pair_second (n k : ℕ) : machine.computer.step (state 2 (n+1) k) =
    some (state 1 n (k+1)) := by
  change some (cfg (1 : Fin 3) () (Function.update (Function.update
    (tapes (List.replicate (n+1) true) (List.replicate k true)) false (List.replicate n true))
    true (true::List.replicate k true))) = _
  congr 2
  funext b; cases b <;> rfl

 theorem zero (k : ℕ) : machine.computer.step (state 1 0 k) =
    some (haltList machine.computer (List.replicate k true)) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,()),Function.update (tapes [] (List.replicate k true)) false []⟩ : machine.Config) = _
  congr 2
  funext b; cases b <;> simp [tapes,wordTape,Function.update]

 theorem one_first (k : ℕ) : machine.computer.step (state 1 1 k) = some (state 2 0 k) := by
  change some (cfg (2 : Fin 3) () (Function.update (tapes [true] (List.replicate k true)) false [])) = _
  congr 2
  funext b; cases b <;> rfl

 theorem one_last (k : ℕ) : machine.computer.step (state 2 0 k) =
    some (haltList machine.computer (List.replicate k true)) := by
  rw [Machine.halt_eq]
  change some (⟨none,(none,()),Function.update (tapes [] (List.replicate k true)) false []⟩ : machine.Config) = _
  congr 2
  funext b; cases b <;> simp [tapes,wordTape,Function.update]

 theorem run (n k : ℕ) : RunsExactly machine.computer.step (state 1 n k)
    (haltList machine.computer (List.replicate (n/2+k) true)) (n+1) := by
  induction n using Nat.twoStepInduction generalizing k with
  | zero => simpa using runsExactly_one (zero k)
  | one => simpa using (runsExactly_one (one_first k)).trans (runsExactly_one (one_last k))
  | more n ih _ =>
    have h := (runsExactly_one (pair_first n k)).trans
      ((runsExactly_one (pair_second n k)).trans (ih (k+1)))
    have he : n/2+(k+1) = (n+2)/2+k := by omega
    simpa only [he,Nat.add_assoc] using h

noncomputable def computes : Computes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding
    (fun n => (n-1)/2) where
  machine := machine
  time := Polynomial.X+2
  outputs n := {
    steps := (n-1+1)+1
    evals_in_steps := by
      have h := (runsExactly_one (first n)).trans (run (n-1) 0)
      change RunsExactly machine.computer.step
        (initList machine.computer (List.replicate n true))
        (haltList machine.computer (List.replicate ((n-1)/2) true)) _
      simpa only [Nat.add_zero] using h
    steps_le_m := by simp [UnaryBinary.unaryEncoding]; omega }

noncomputable def graphComputes : Computes RawClosedNetwork.encoding UnaryBinary.unaryEncoding
    (fun G => (Paper2.BellReduction.RawOccurrence.markedCount G.vertices-1)/2) :=
  (RawTriple.markedComputes.andThen (Lists.lengthUnaryComputes RawClosedNetwork.vertexEncoding)).andThen computes

end Paper2.Complexity.BellMachines.UnaryRounds
