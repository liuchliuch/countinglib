import Counting.Algorithm.KarpLubyRequest.Sampling.RowSemantics
import Holant.Complexity.GraphPreprocessing.Primitive

/-!
# A finite scanner for clause unranking

The input row is the actual two-bit dense cell word. The rank is a physical
little-endian stack. A free cell pops one rank bit (empty means false); a fixed
cell reads its stored bit. The assignment is reversed once to restore variable
order. There are four Boolean stacks, three labels and three control states.
All theorem parameters occur in execution specifications, never in the machine
control or its transition function.
-/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.Unrank
open Turing Computability Holant.Complexity StackProtocol
open RowSemantics

abbrev Stack := Fin 4
abbrev Label := Fin 3
abbrev State := Option Bool × Unit

def tapes (row rank reversed output : List Bool) : Stack → List Bool :=
  ![row, rank, reversed, output]

def config (label : Label) (row rank reversed output : List Bool) : Cfg Stack Label Unit :=
  cfg label () (tapes row rank reversed output)

/-- Both branches physically read the second cell bit; only a free cell pops rank. -/
def scan : Stmt Stack Label Unit :=
  .pop 0 (fun v b => (b, v.2))
    (.branch (fun v => v.1.isSome)
      (.branch (fun v => v.1.getD false)
        (.pop 0 (fun v b => (b, v.2))
          (.push 2 (fun v => v.1.getD false)
            (.load (fun v => (none, v.2)) (.goto (fun _ => 0)))))
        (.pop 0 (fun v _ => v)
          (.pop 1 (fun v b => (b, v.2))
            (.push 2 (fun v => v.1.getD false)
              (.load (fun v => (none, v.2)) (.goto (fun _ => 0)))))))
      (.load (fun v => (none, v.2)) (.goto (fun _ => 1))))

def program (label : Label) : Stmt Stack Label Unit :=
  if label = 0 then scan
  else if label = 1 then copyMoveStmt 2 3 1 2
  else .halt

abbrev computer : FinTM2 where
  K := Stack
  k₀ := 0
  k₁ := 3
  Γ _ := Bool
  Λ := Label
  main := 0
  σ := State
  initialState := (none, ())
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

private theorem update_tapes (row rank reversed output word : List Bool) (i : Fin 4) :
    Function.update (tapes row rank reversed output) i word =
      tapes (if i = 0 then word else row) (if i = 1 then word else rank)
        (if i = 2 then word else reversed) (if i = 3 then word else output) := by
  funext j; fin_cases i <;> fin_cases j <;> rfl

theorem step_free (row rank reversed output : List Bool) :
    computer.step (config 0 (false :: false :: row) rank reversed output) =
      some (config 0 row rank.tail (rank.head?.getD false :: reversed) output) := by
  cases rank <;>
    simp [FinTM2.step, TM2.step, program, scan, config, cfg, TM2.stepAux,
      update_tapes, tapes]
  all_goals congr 2; funext k; fin_cases k <;> rfl

theorem step_fixed (b : Bool) (row rank reversed output : List Bool) :
    computer.step (config 0 (true :: b :: row) rank reversed output) =
      some (config 0 row rank (b :: reversed) output) := by
  simp [FinTM2.step, TM2.step, program, scan, config, cfg, TM2.stepAux,
    update_tapes, tapes]
  congr 2; funext k; fin_cases k <;> rfl

theorem step_done (rank reversed output : List Bool) :
    computer.step (config 0 [] rank reversed output) =
      some (config 1 [] rank reversed output) := by
  simp [FinTM2.step, TM2.step, program, scan, config, cfg, TM2.stepAux, update_tapes, tapes]
  congr 2; funext k; fin_cases k <;> rfl

/-- Each row cell executes one transition; both physical symbols are charged by
the primitive interpreter. The final empty-row test is also included. -/
theorem scan_exact (xs : Cells) (rank reversed output : List Bool) :
    RunsExactly computer.step (config 0 (Dense.CellCodec.encode xs) rank reversed output)
      (config 1 [] (rank.drop (free xs)) ((bits xs rank).reverse ++ reversed) output)
      (xs.length + 1) := by
  induction xs generalizing rank reversed with
  | nil => simpa only [Dense.CellCodec.encode_nil, free, bits, List.drop_zero,
      List.reverse_nil, List.nil_append, List.length_nil, Nat.zero_add] using
      runsExactly_one (step_done rank reversed output)
  | cons x xs ih =>
    cases x with
    | none =>
      have hr := (runsExactly_one (step_free (Dense.CellCodec.encode xs) rank reversed output)).trans
        (ih rank.tail (rank.head?.getD false :: reversed))
      have hd : rank.tail.drop (free xs) = rank.drop (free xs + 1) := by
        cases rank <;> simp
      simpa only [Dense.CellCodec.encode_cons, Dense.CellCodec.cell, List.cons_append,
        List.nil_append, free, bits, List.reverse_cons, List.append_assoc,
        List.singleton_append, List.length_cons, hd] using hr
    | some b =>
      have hr := (runsExactly_one (step_fixed b (Dense.CellCodec.encode xs) rank reversed output)).trans
        (ih rank (b :: reversed))
      simpa only [Dense.CellCodec.encode_cons, Dense.CellCodec.cell, List.cons_append,
        List.nil_append, free, bits, List.reverse_cons, List.append_assoc,
        List.singleton_append, List.length_cons] using hr

private theorem tapes_as_copy (row rank reversed output : List Bool) :
    tapes row rank reversed output =
      tapes3 (tapes row [] [] []) (2 : Stack) 1 3 reversed rank output := by
  funext k; fin_cases k <;> rfl

theorem restore_exact (row rank reversed output : List Bool) :
    RunsExactly computer.step (config 1 row rank reversed output)
      (config 2 row rank [] (reversed.reverse ++ output)) (reversed.length + 1) := by
  have he : ExecutesAt computer.step (1 : Label) (copyMoveStmt (2 : Stack) 3 1 2) := by
    intro state tape; rfl
  simpa only [config, ← tapes_as_copy] using
    copy_move_exact (2 : Stack) 1 3 (by decide) (by decide) computer.step (1 : Label) 2
      he () (tapes row [] [] []) reversed rank output

/-- The exact returning run implements the original clause sampler, and leaves
unused high rank bits available to the surrounding caller. -/
theorem returns (xs : Cells) (r : ℕ) (output : List Bool) :
    RunsExactly computer.step (config 0 (Dense.CellCodec.encode xs) (encodeNat r) [] output)
      (config 2 [] ((encodeNat r).drop (free xs)) []
        (List.ofFn (Counting.Algorithm.KarpLuby.DNF.sampleNat
          (Counting.Algorithm.KarpLubyMachine.DenseNormalization.denote xs.length xs) r) ++ output))
      (2 * xs.length + 2) := by
  have hs := scan_exact xs (encodeNat r) [] output
  simp only [List.append_nil] at hs
  have hr := restore_exact [] ((encodeNat r).drop (free xs)) (bits xs (encodeNat r)).reverse output
  have h := hs.trans hr
  simp only [List.reverse_reverse, List.length_reverse, bits_length] at h
  rw [bits_original] at h
  convert h using 1 <;> omega

theorem statement_budget (label : Label) : TM2Cost.budget (program label) ≤ 8 := by
  fin_cases label <;> decide

/-- Costs are accumulated by the primitive interpreter on exactly the run above. -/
theorem primitive_cost (xs : Cells) (r : ℕ) (output : List Bool) :
    (GraphPreprocessing.Primitive.run program (2 * xs.length + 2)
      (some (config 0 (Dense.CellCodec.encode xs) (encodeNat r) [] output))).2 =
      some (config 2 [] ((encodeNat r).drop (free xs)) []
        (List.ofFn (Counting.Algorithm.KarpLuby.DNF.sampleNat
          (Counting.Algorithm.KarpLubyMachine.DenseNormalization.denote xs.length xs) r) ++ output)) ∧
    (GraphPreprocessing.Primitive.run program (2 * xs.length + 2)
      (some (config 0 (Dense.CellCodec.encode xs) (encodeNat r) [] output))).1 ≤
      8 * (2 * xs.length + 2) :=
  GraphPreprocessing.Primitive.execution_cost program 8 statement_budget _ _ _ (returns xs r output)

end Counting.Algorithm.KarpLubyRequest.Sampling.Unrank
