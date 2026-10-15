import Counting.Algorithm.KarpLubyRequest.Dense.FormulaTermCall

/-! # Existing unary-to-binary machine as the actual final clause-count call -/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Formula
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open IntegerArithmetic

/-- Final prepared output: canonical binary count and ordered framed rows,
with both original input words retained and every work stack cleared. -/
def outputBank (original formula count rows : List Bool) : Fin 13 → List Bool :=
  fun k => match k.val with
    | 0 => original
    | 4 => count
    | 8 => formula
    | 12 => rows
    | _ => []

@[simp] theorem countStacks_0 : countStacks 0 = 11 := rfl
@[simp] theorem countStacks_1 : countStacks 1 = 4 := rfl
@[simp] theorem countStacks_2 : countStacks 2 = 6 := rfl

private def countEnd (word : List Bool) : UnaryBinary.machine.Config :=
  ⟨none, CarryProtocol.clean (false, false), UnaryBinary.tapes [] word []⟩

private theorem count_source (tokens : List Bool) :
    (fun c => c.bind (TM2.step UnaryBinary.machine.program))^[1 + UnaryBinary.ticks [] tokens.length]
      (some (UnaryBinary.config 0 tokens [] [])) = some (countEnd (encodeNat tokens.length)) := by
  have first := UnaryBinary.convert_exact tokens 0
  simp only [Nat.zero_add, show encodeNat 0 = [] from rfl] at first
  have last : TM2.step UnaryBinary.machine.program (UnaryBinary.config 3 [] (encodeNat tokens.length) []) =
      some (countEnd (encodeNat tokens.length)) := by rfl
  exact first.trans (UnaryBinary.Runs.one last)

private theorem outside_countStacks (k : Fin 13)
    (h11 : k ≠ 11) (h4 : k ≠ 4) (h6 : k ≠ 6) :
    ∀ i : Fin 3, k ≠ countStacks i := by
  intro i
  refine Fin.cases h11 ?_ i
  intro i
  refine Fin.cases h4 ?_ i
  intro i
  exact Fin.cases h6 (fun j => Fin.elim0 j) i

private theorem stack_ne (a b : Fin 13) (h : a.val ≠ b.val) : a ≠ b :=
  fun e => h (congrArg Fin.val e)

private theorem count_bank_eq (tape : Fin 13 → List Bool)
    (original formula word tokens rows : List Bool)
    (ht : ∀ i : Fin 3, tape (countStacks i) = (![[], word, []] : Fin 3 → List Bool) i)
    (hf : ∀ k : Fin 13, (∀ i : Fin 3, k ≠ countStacks i) →
      tape k = bank original formula [] [] [] [] tokens rows k) :
    tape = outputBank original formula word rows := by
  funext k
  refine Fin.cases (hf 0 (outside_countStacks 0 (stack_ne 0 11 (of_decide_eq_true rfl)) (stack_ne 0 4 (of_decide_eq_true rfl)) (stack_ne 0 6 (of_decide_eq_true rfl)))) ?_ k
  intro k
  refine Fin.cases (hf 1 (outside_countStacks 1 (stack_ne 1 11 (of_decide_eq_true rfl)) (stack_ne 1 4 (of_decide_eq_true rfl)) (stack_ne 1 6 (of_decide_eq_true rfl)))) ?_ k
  intro k
  refine Fin.cases (hf 2 (outside_countStacks 2 (stack_ne 2 11 (of_decide_eq_true rfl)) (stack_ne 2 4 (of_decide_eq_true rfl)) (stack_ne 2 6 (of_decide_eq_true rfl)))) ?_ k
  intro k
  refine Fin.cases (hf 3 (outside_countStacks 3 (stack_ne 3 11 (of_decide_eq_true rfl)) (stack_ne 3 4 (of_decide_eq_true rfl)) (stack_ne 3 6 (of_decide_eq_true rfl)))) ?_ k
  intro k
  refine Fin.cases (ht 1) ?_ k
  intro k
  refine Fin.cases (hf 5 (outside_countStacks 5 (stack_ne 5 11 (of_decide_eq_true rfl)) (stack_ne 5 4 (of_decide_eq_true rfl)) (stack_ne 5 6 (of_decide_eq_true rfl)))) ?_ k
  intro k
  refine Fin.cases (ht 2) ?_ k
  intro k
  refine Fin.cases (hf 7 (outside_countStacks 7 (stack_ne 7 11 (of_decide_eq_true rfl)) (stack_ne 7 4 (of_decide_eq_true rfl)) (stack_ne 7 6 (of_decide_eq_true rfl)))) ?_ k
  intro k
  refine Fin.cases (hf 8 (outside_countStacks 8 (stack_ne 8 11 (of_decide_eq_true rfl)) (stack_ne 8 4 (of_decide_eq_true rfl)) (stack_ne 8 6 (of_decide_eq_true rfl)))) ?_ k
  intro k
  refine Fin.cases (hf 9 (outside_countStacks 9 (stack_ne 9 11 (of_decide_eq_true rfl)) (stack_ne 9 4 (of_decide_eq_true rfl)) (stack_ne 9 6 (of_decide_eq_true rfl)))) ?_ k
  intro k
  refine Fin.cases (hf 10 (outside_countStacks 10 (stack_ne 10 11 (of_decide_eq_true rfl)) (stack_ne 10 4 (of_decide_eq_true rfl)) (stack_ne 10 6 (of_decide_eq_true rfl)))) ?_ k
  intro k
  refine Fin.cases (ht 0) ?_ k
  intro k
  refine Fin.cases (hf 12 (outside_countStacks 12 (stack_ne 12 11 (of_decide_eq_true rfl)) (stack_ne 12 4 (of_decide_eq_true rfl)) (stack_ne 12 6 (of_decide_eq_true rfl)))) ?_ k
  exact fun i => Fin.elim0 i

private theorem count_returned_eq
    (ending : Cfg (Fin 13) Label (Bool × CarryProtocol.Memory))
    (bit : Bool) (original formula tokens rows : List Bool)
    (h : Embedded.Rel countStacks Label.count .good (bank original formula [] [] [] [] tokens rows)
      (StateAdapter.cfg countState (none, bit) (countEnd (encodeNat tokens.length))) ending) :
    ending = cfg .good (cleanMemory bit) (outputBank original formula (encodeNat tokens.length) rows) := by
  rcases ending with ⟨label, state, tape⟩
  rcases h with ⟨hl, hv, ht, hf⟩
  change label = some Label.good at hl
  change state = (none, cleanMemory bit) at hv
  subst label state
  have bank_eq := count_bank_eq tape original formula (encodeNat tokens.length) tokens rows ht hf
  change TM2.Cfg.mk (some Label.good) (none, cleanMemory bit) tape =
    TM2.Cfg.mk (some Label.good) (none, cleanMemory bit) (outputBank original formula (encodeNat tokens.length) rows)
  rw [bank_eq]

/-- No decoded count occurs in control: each physically emitted unary token is
consumed by the existing H1 increment/carry program. -/
theorem count_call (bit : Bool) (original formula tokens rows : List Bool) :
    RunsExactly computer.step
      (cfg (.count 0) (cleanMemory bit) (bank original formula [] [] [] [] tokens rows))
      (cfg .good (cleanMemory bit) (outputBank original formula (encodeNat tokens.length) rows))
      (1 + UnaryBinary.ticks [] tokens.length) := by
  have source := StateAdapter.run countState UnaryBinary.machine.program (none, bit)
    (UnaryBinary.config 0 tokens [] []) (countEnd (encodeNat tokens.length))
    (1 + UnaryBinary.ticks [] tokens.length) (count_source tokens)
  have initial : Embedded.Rel countStacks Label.count .good
      (bank original formula [] [] [] [] tokens rows)
      (StateAdapter.cfg countState (none, bit) (UnaryBinary.config 0 tokens [] []))
      (cfg (.count 0) (cleanMemory bit) (bank original formula [] [] [] [] tokens rows)) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro i
      refine Fin.cases rfl ?_ i
      intro i
      refine Fin.cases rfl ?_ i
      intro i
      exact Fin.cases rfl (fun j => Fin.elim0 j) i
    · intro k hk; rfl
  obtain ⟨ending, actual, relation⟩ := Embedded.run countStacks Label.count .good
    (StateAdapter.program countState UnaryBinary.machine.program) program
    (by intro l; rfl) _ _ _ (bank original formula [] [] [] [] tokens rows)
    (1 + UnaryBinary.ticks [] tokens.length) initial source
  rw [count_returned_eq ending bit original formula tokens rows relation] at actual
  exact actual

theorem count_call_bound (tokens : List Bool) :
    1 + UnaryBinary.ticks [] tokens.length ≤ 2 * tokens.length ^ 2 + 5 * tokens.length + 4 := by
  have h := UnaryBinary.ticks_le [] tokens.length
  simp only [List.length_nil, Nat.zero_add] at h
  nlinarith

end Counting.Algorithm.KarpLubyRequest.Dense.Formula
