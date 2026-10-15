import Counting.Algorithm.KarpLubyRequest.Dense.WriteRun

/-! # Concrete finite dense-row writer -/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Write
open Turing Computability Holant.Complexity StackProtocol
open Turing.TM2.Stmt
open Counting.Algorithm.KarpLubyMachine

def localStacks : Stacks (Fin 4) := ⟨id, fun _ _ h => h⟩
def localLabels : Labels (Fin 11) := ⟨0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10⟩

def program (label : Fin 11) : Stmt (Fin 4) (Fin 11) (Bool × Unit) :=
  if label = 0 then checkStmt 0 1 1 4 6
  else if label = 1 then skipStmt 0 2 2
  else if label = 2 then CountedList.Counter.decrementStmt 1 3 2 3
  else if label = 3 then copyMoveStmt 3 1 3 0
  else if label = 4 then writeStmt 0 5 6
  else if label = 5 then copyMoveStmt 2 0 5 9
  else if label = 6 then clearStmt 1 6 7
  else if label = 7 then clearStmt 2 7 8
  else if label = 8 then clearStmt 0 8 10
  else halt

/-- The literal is one Boolean register, never a decoded index or row. -/
abbrev computer (b : Bool) : FinTM2 where
  K := Fin 4
  k₀ := 0
  k₁ := 0
  Γ _ := Bool
  Λ := Fin 11
  main := 0
  σ := Option Bool × (Bool × Unit)
  initialState := (none, (b, ()))
  m := program

instance alphabetFintype (b : Bool) (k : (computer b).K) : Fintype ((computer b).Γ k) :=
  inferInstanceAs (Fintype Bool)

theorem statement_budget (label : Fin 11) : TM2Cost.budget (program label) ≤ 8 := by
  fin_cases label <;> decide

theorem computer_executes (b : Bool) : Executes (computer b).step localStacks localLabels := by
  constructor <;> intro state tape <;> rfl

/-- A prepared call with an actual encoded index. The returned label distinguishes
success from conflict, including when the desired row itself is empty. -/
theorem computer_returns (b : Bool) (xs : CellCodec.Cells) (j : ℕ) :
    ∃ time : ℕ,
      time ≤ (xs.length + 1) * (2 * (encodeNat j).length + 6) + 3 ∧
      RunsExactly (computer b).step
        (cfg (0 : Fin 11) (b, ())
          (tapes localStacks (fun _ => []) (CellCodec.encode xs) (encodeNat j) [] []))
        (finished localStacks localLabels b () (fun _ => []) []
          (DenseNormalization.write j b xs).value) time := by
  simpa only [localLabels, List.length_nil, Nat.mul_zero, Nat.add_zero,
    CellCodec.encode_nil, List.reverse_nil] using
    write_returns (computer b).step localStacks localLabels (computer_executes b)
      b () (fun _ => []) xs [] j

/-- The same exact returning execution also has a primitive-interpreter bound. -/
theorem computer_primitive_cost (b : Bool) (xs : CellCodec.Cells) (j : ℕ) :
    ∃ time : ℕ,
      time ≤ (xs.length + 1) * (2 * (encodeNat j).length + 6) + 3 ∧
      (GraphPreprocessing.Primitive.run program time
        (some (cfg (0 : Fin 11) (b, ())
          (tapes localStacks (fun _ => []) (CellCodec.encode xs) (encodeNat j) [] [])))).2 =
        some (finished localStacks localLabels b () (fun _ => []) []
          (DenseNormalization.write j b xs).value) ∧
      (GraphPreprocessing.Primitive.run program time
        (some (cfg (0 : Fin 11) (b, ())
          (tapes localStacks (fun _ => []) (CellCodec.encode xs) (encodeNat j) [] [])))).1 ≤ 8 * time := by
  obtain ⟨time, bound, run⟩ := computer_returns b xs j
  exact ⟨time, bound, GraphPreprocessing.Primitive.execution_cost program 8 statement_budget _ _ _ run⟩

end Counting.Algorithm.KarpLubyRequest.Dense.Write
