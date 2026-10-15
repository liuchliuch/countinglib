import Counting.Algorithm.KarpLubyRequest.Sampling.RowSemantics
import Holant.Complexity.GraphPreprocessing.Primitive

/-!
# Physical construction of a clause's binary mass

One initial bit represents one. The scanner reads both symbols of each dense
cell, prepending a false bit exactly for a free coordinate. Thus an exponential
cardinality is constructed in linear time in the number of declared variables,
without enumerating assignments or iterating to the value of the cardinality.
-/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.RowMass
open Turing Computability Holant.Complexity StackProtocol
open RowSemantics

abbrev Stack := Fin 2
abbrev Label := Fin 3

def tapes (row mass : List Bool) : Stack → List Bool := ![row, mass]
def config (label : Label) (row mass : List Bool) : Cfg Stack Label Unit :=
  cfg label () (tapes row mass)

def scan : Stmt Stack Label Unit :=
  .pop 0 (fun v bit => (bit, v.2))
    (.branch (fun v => v.1.isSome)
      (.branch (fun v => v.1.getD false)
        (.pop 0 (fun v _ => v)
          (.load (fun v => (none, v.2)) (.goto (fun _ => 1))))
        (.pop 0 (fun v _ => v)
          (.push 1 (fun _ => false)
            (.load (fun v => (none, v.2)) (.goto (fun _ => 1))))))
      (.load (fun v => (none, v.2)) (.goto (fun _ => 2))))

def program (label : Label) : Stmt Stack Label Unit :=
  if label = 0 then .push 1 (fun _ => true) (.goto (fun _ => 1))
  else if label = 1 then scan
  else .halt

abbrev computer : FinTM2 where
  K := Stack
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Label
  main := 0
  σ := Option Bool × Unit
  initialState := (none, ())
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

theorem step_start (row mass : List Bool) :
    computer.step (config 0 row mass) = some (config 1 row (true :: mass)) := by
  simp [FinTM2.step, TM2.step, program, config, cfg, TM2.stepAux, tapes]
  congr 2; funext k; fin_cases k <;> rfl

theorem step_free (row mass : List Bool) :
    computer.step (config 1 (false :: false :: row) mass) =
      some (config 1 row (false :: mass)) := by
  simp [FinTM2.step, TM2.step, program, scan, config, cfg, TM2.stepAux, tapes]
  congr 2; funext k; fin_cases k <;> rfl

theorem step_fixed (b : Bool) (row mass : List Bool) :
    computer.step (config 1 (true :: b :: row) mass) = some (config 1 row mass) := by
  simp [FinTM2.step, TM2.step, program, scan, config, cfg, TM2.stepAux, tapes]
  congr 2; funext k; fin_cases k <;> rfl

theorem step_done (mass : List Bool) :
    computer.step (config 1 [] mass) = some (config 2 [] mass) := by
  simp [FinTM2.step, TM2.step, program, scan, config, cfg, TM2.stepAux, tapes]
  congr 2; funext k; fin_cases k <;> rfl

/-- All cells are physically scanned, including fixed and unused coordinates. -/
theorem scan_exact (xs : Cells) (mass : List Bool) :
    RunsExactly computer.step (config 1 (Dense.CellCodec.encode xs) mass)
      (config 2 [] (List.replicate (free xs) false ++ mass)) (xs.length + 1) := by
  induction xs generalizing mass with
  | nil => simpa only [Dense.CellCodec.encode_nil, free, List.replicate_zero,
      List.nil_append, List.length_nil, Nat.zero_add] using runsExactly_one (step_done mass)
  | cons x xs ih =>
    cases x with
    | none =>
      have hr := (runsExactly_one (step_free (Dense.CellCodec.encode xs) mass)).trans (ih (false :: mass))
      have he : List.replicate (free xs) false ++ false :: mass =
          List.replicate (free xs + 1) false ++ mass := by
        rw [List.replicate_add, List.append_assoc]
        rfl
      simpa only [Dense.CellCodec.encode_cons, Dense.CellCodec.cell, List.cons_append,
        List.nil_append, free, List.length_cons, he] using hr
    | some b =>
      simpa only [Dense.CellCodec.encode_cons, Dense.CellCodec.cell, List.cons_append,
        List.nil_append, free, List.length_cons] using
        (runsExactly_one (step_fixed b (Dense.CellCodec.encode xs) mass)).trans (ih mass)

theorem power_word (n : ℕ) : List.replicate n false ++ [true] = encodeNat (2 ^ n) := by
  apply BinaryArithmetic.canonical_injective
  · induction n with
    | zero => exact ⟨trivial, fun _ => rfl⟩
    | succ n ih =>
      rw [List.replicate_succ, List.cons_append]
      exact ⟨ih, by simp⟩
  · exact BinaryArithmetic.canonical_encodeNat _
  · rw [BinaryArithmetic.value_encodeNat]
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [List.replicate_succ, List.cons_append, BinaryArithmetic.value_cons,
        Bool.toNat_false, Nat.zero_add, ih, pow_succ]
      omega

/-- Binary mass construction has one transition per cell plus initialization and
the empty-row test. No loop is proportional to the numeric value `2^free`. -/
theorem returns (xs : Cells) :
    RunsExactly computer.step (config 0 (Dense.CellCodec.encode xs) [])
      (config 2 [] (encodeNat (Counting.Algorithm.KarpLuby.DNF.clauseMass
        (Counting.Algorithm.KarpLubyMachine.DenseNormalization.denote xs.length xs))))
      (xs.length + 2) := by
  have hr := (runsExactly_one (step_start (Dense.CellCodec.encode xs) [])).trans (scan_exact xs [true])
  rw [power_word] at hr
  dsimp only [Counting.Algorithm.KarpLuby.DNF.clauseMass]
  rw [free_denote]
  exact hr

theorem statement_budget (label : Label) : TM2Cost.budget (program label) ≤ 7 := by
  fin_cases label <;> decide

/-- Include the real halt instruction, for embedding this source into a caller. -/
theorem halt_exact (xs : Cells) :
    RunsExactly computer.step (config 0 (Dense.CellCodec.encode xs) [])
      (⟨none, (none, ()), tapes [] (encodeNat (2 ^ free xs))⟩ : Cfg Stack Label Unit)
      (xs.length + 3) := by
  have hr := returns xs
  dsimp only [Counting.Algorithm.KarpLuby.DNF.clauseMass] at hr
  rw [free_denote] at hr
  have hs : computer.step (config 2 [] (encodeNat (2 ^ free xs))) =
      some (⟨none, (none, ()), tapes [] (encodeNat (2 ^ free xs))⟩ : Cfg Stack Label Unit) := rfl
  convert hr.trans (runsExactly_one hs) using 1 <;> omega

theorem primitive_cost (xs : Cells) :
    (GraphPreprocessing.Primitive.run program (xs.length + 2)
      (some (config 0 (Dense.CellCodec.encode xs) []))).2 =
      some (config 2 [] (encodeNat (Counting.Algorithm.KarpLuby.DNF.clauseMass
        (Counting.Algorithm.KarpLubyMachine.DenseNormalization.denote xs.length xs)))) ∧
    (GraphPreprocessing.Primitive.run program (xs.length + 2)
      (some (config 0 (Dense.CellCodec.encode xs) []))).1 ≤ 7 * (xs.length + 2) :=
  GraphPreprocessing.Primitive.execution_cost program 7 statement_budget _ _ _ (returns xs)

end Counting.Algorithm.KarpLubyRequest.Sampling.RowMass
