import Counting.Algorithm.KarpLubyRequest.Dense.FormulaProgram

/-! # Exact compiler call to the finite term normalizer, preserving the formula bank -/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Formula
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

/-- Clean phase-boundary bank. The five term scratch stacks are empty. -/
def bank (original formula work term row reverseRows tokens output : List Bool) : Fin 13 → List Bool :=
  fun k => match k.val with
    | 0 => original
    | 1 => term
    | 2 => row
    | 8 => formula
    | 9 => work
    | 10 => reverseRows
    | 11 => tokens
    | 12 => output
    | _ => []

abbrev cleanMemory (bit : Bool) : Bool × IntegerArithmetic.CarryProtocol.Memory :=
  (bit, IntegerArithmetic.CarryProtocol.clean (false, false))

@[simp] theorem termStacks_apply (i : Fin 8) : termStacks i = ⟨i.val, by omega⟩ := rfl

private theorem returned_eq (ending : Cfg (Fin 13) Label (Bool × IntegerArithmetic.CarryProtocol.Memory))
    (original formula work raw reverseRows tokens output : List Bool) (result : Option CellCodec.Cells)
    (h : Embedded.Rel termStacks Label.term .afterTerm
      (bank original formula work raw [] reverseRows tokens output)
      (Normalize.returned (IntegerArithmetic.CarryProtocol.clean (false, false)) original result) ending) :
    ending = cfg .afterTerm (cleanMemory result.isSome)
      (bank original formula work [] (result.elim [] CellCodec.encode) reverseRows tokens output) := by
  rcases ending with ⟨label, state, tape⟩
  rcases h with ⟨hl, hv, ht, hf⟩
  change label = some Label.afterTerm at hl
  change state = (none, cleanMemory result.isSome) at hv
  subst label state
  unfold cfg
  congr 1
  funext k
  fin_cases k
  · simpa [Normalize.returned, Normalize.tapes, bank] using ht (0 : Fin 8)
  · simpa [Normalize.returned, Normalize.tapes, bank] using ht (1 : Fin 8)
  · simpa [Normalize.returned, Normalize.tapes, bank] using ht (2 : Fin 8)
  · simpa [Normalize.returned, Normalize.tapes, bank] using ht (3 : Fin 8)
  · simpa [Normalize.returned, Normalize.tapes, bank] using ht (4 : Fin 8)
  · simpa [Normalize.returned, Normalize.tapes, bank] using ht (5 : Fin 8)
  · simpa [Normalize.returned, Normalize.tapes, bank] using ht (6 : Fin 8)
  · simpa [Normalize.returned, Normalize.tapes, bank] using ht (7 : Fin 8)
  · exact hf 8 (by intro i h; have hv := congrArg Fin.val h; change 8 = i.val at hv; omega)
  · exact hf 9 (by intro i h; have hv := congrArg Fin.val h; change 9 = i.val at hv; omega)
  · exact hf 10 (by intro i h; have hv := congrArg Fin.val h; change 10 = i.val at hv; omega)
  · exact hf 11 (by intro i h; have hv := congrArg Fin.val h; change 11 = i.val at hv; omega)
  · exact hf 12 (by intro i h; have hv := congrArg Fin.val h; change 12 = i.val at hv; omega)

/-- Generated source instructions are the caller's actual instructions, with
exactly the source transition count. Original formula, remaining terms, rows,
count tokens, and already emitted output are all preserved by the call. -/
theorem term_call (old : Bool) (original formula work raw reverseRows tokens output : List Bool)
    (term : DNF.RawTerm original.length)
    (hdecode : (Encoding.list (Encoding.literal original.length)).decode raw = some term) :
    ∃ time : ℕ, time ≤ Normalize.rawCost original.length raw.length + 1 ∧
      RunsExactly computer.step
        (cfg (.term .headerScan) (cleanMemory old)
          (bank original formula work raw [] reverseRows tokens output))
        (cfg .afterTerm (cleanMemory (DenseNormalization.normalize original.length term).value.isSome)
          (bank original formula work []
            ((DenseNormalization.normalize original.length term).value.elim [] CellCodec.encode)
            reverseRows tokens output)) time := by
  obtain ⟨time, bound, run⟩ := Normalize.normalize_call old
    (IntegerArithmetic.CarryProtocol.clean (false, false)) original raw term hdecode
  have initial : Embedded.Rel termStacks Label.term .afterTerm
      (bank original formula work raw [] reverseRows tokens output)
      (cfg Normalize.Label.headerScan (cleanMemory old) (Normalize.tapes original raw [] [] [] [] [] []))
      (cfg (Label.term .headerScan) (cleanMemory old) (bank original formula work raw [] reverseRows tokens output)) := by
    refine ⟨rfl, rfl, ?_, ?_⟩
    · intro i; fin_cases i <;> rfl
    · intro k hk; rfl
  obtain ⟨ending, actual, relation⟩ := Embedded.run termStacks Label.term .afterTerm
    (Normalize.program (τ := IntegerArithmetic.CarryProtocol.Memory)) program
    (by intro l; rfl) _ _ _ (bank original formula work raw [] reverseRows tokens output) time initial run
  rw [returned_eq ending original formula work raw reverseRows tokens output _ relation] at actual
  exact ⟨time, bound, actual⟩

end Counting.Algorithm.KarpLubyRequest.Dense.Formula
