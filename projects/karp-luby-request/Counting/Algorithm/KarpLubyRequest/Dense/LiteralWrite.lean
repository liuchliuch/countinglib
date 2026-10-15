import Counting.Algorithm.KarpLubyRequest.Dense.WriteMachine
import Counting.Algorithm.KarpLubyRequest.LiteralFields

/-!
# A raw literal drives an actual checked row write

The raw natural word is extracted, canonicalized using the original total
`decodeNat`, and placed on the writer's binary counter stack. The polarity is
popped into a single Boolean register. A successful literal decoder premise can
supply the range condition, but the row writer also rejects out-of-bounds inputs.
-/
namespace Counting.Algorithm.KarpLubyRequest.Dense.LiteralWrite
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Turing.TM2.Stmt
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

variable {K Λ τ : Type} [DecidableEq K]
/-- Raw literal, row, raw index, canonical index, row pref, shared scratch. -/
abbrev Stacks (K : Type) := Fin 6 ↪ K

def tapes (st : Stacks K) (frame : K → List Bool)
    (source row raw counter pref scratch : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update frame (st 0) source) (st 1) row) (st 2) raw)
      (st 3) counter) (st 4) pref) (st 5) scratch

@[simp] theorem tapes_at (st : Stacks K) (frame : K → List Bool)
    (source row raw counter pref scratch : List Bool) (i : Fin 6) :
    tapes st frame source row raw counter pref scratch (st i) =
      (![source, row, raw, counter, pref, scratch] : Fin 6 → List Bool) i := by
  fin_cases i <;> simp [tapes, st.injective.eq_iff]

structure Labels (Λ : Type) where
  scan : Λ
  restore : Λ
  naturalMove : Λ
  naturalHighest : Λ
  naturalRestore : Λ
  polarity : Λ
  writer : Write.Labels Λ

def naturalStacks (st : Stacks K) : NaturalWords.Stacks K :=
  ⟨fun i => st (![2, 3, 5] i), by
    intro a b h
    have hi := st.injective h
    fin_cases a <;> fin_cases b <;> simp_all⟩

def naturalLabels (lab : Labels Λ) : NaturalWords.Labels Λ :=
  ⟨lab.naturalMove, lab.naturalHighest, lab.naturalRestore, lab.polarity⟩

def writeStacks (st : Stacks K) : Write.Stacks K :=
  ⟨fun i => st (![1, 3, 4, 5] i), by
    intro a b h
    have hi := st.injective h
    fin_cases a <;> fin_cases b <;> simp_all⟩

@[simp] theorem naturalStacks_0 (st : Stacks K) : naturalStacks st 0 = st 2 := rfl
@[simp] theorem naturalStacks_1 (st : Stacks K) : naturalStacks st 1 = st 3 := rfl
@[simp] theorem naturalStacks_2 (st : Stacks K) : naturalStacks st 2 = st 5 := rfl
@[simp] theorem writeStacks_0 (st : Stacks K) : writeStacks st 0 = st 1 := rfl
@[simp] theorem writeStacks_1 (st : Stacks K) : writeStacks st 1 = st 3 := rfl
@[simp] theorem writeStacks_2 (st : Stacks K) : writeStacks st 2 = st 4 := rfl
@[simp] theorem writeStacks_3 (st : Stacks K) : writeStacks st 3 = st 5 := rfl

/-- Successful raw-literal parsing guarantees a singleton polarity stack.
The program still reads that physical bit instead of receiving it semantically. -/
def polarityStmt (source : K) (next : Λ) : Stmt K Λ (Bool × τ) :=
  pop source (fun v bit => (none, (bit.getD false, v.2.2))) (goto (fun _ => next))

structure Executes (step : Cfg K Λ (Bool × τ) → Option (Cfg K Λ (Bool × τ)))
    (st : Stacks K) (lab : Labels Λ) : Prop where
  scan : ExecutesAt step lab.scan (Frame.scanStmt (st 0) (st 5) lab.scan lab.restore lab.writer.bad)
  restore : ExecutesAt step lab.restore (copyMoveStmt (st 5) (st 2) lab.restore lab.naturalMove)
  natural : NaturalWords.Executes step (naturalStacks st) (naturalLabels lab)
  polarity : ExecutesAt step lab.polarity (polarityStmt (st 0) lab.writer.loop)
  writer : Write.Executes step (writeStacks st) lab.writer

private theorem as_frame (st : Stacks K) (frame : K → List Bool)
    (source row raw counter pref scratch : List Bool) :
    tapes st frame source row raw counter pref scratch =
      tapes3 (tapes st frame [] row [] counter pref []) (st 0) (st 2) (st 5) source raw scratch := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;> by_cases h2 : k = st 2 <;>
    by_cases h3 : k = st 3 <;> by_cases h4 : k = st 4 <;> by_cases h5 : k = st 5 <;>
    simp_all [tapes, tapes3, Function.update_apply, st.injective.eq_iff]

private theorem as_natural (st : Stacks K) (frame : K → List Bool)
    (source row raw counter pref scratch : List Bool) :
    tapes st frame source row raw counter pref scratch =
      NaturalWords.tapes (naturalStacks st) (tapes st frame source row [] [] pref []) raw counter scratch := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;> by_cases h2 : k = st 2 <;>
    by_cases h3 : k = st 3 <;> by_cases h4 : k = st 4 <;> by_cases h5 : k = st 5 <;>
    simp_all [tapes, NaturalWords.tapes, tapes3, Function.update_apply, st.injective.eq_iff]

private theorem as_writer (st : Stacks K) (frame : K → List Bool)
    (source row raw counter pref scratch : List Bool) :
    tapes st frame source row raw counter pref scratch =
      Write.tapes (writeStacks st) (tapes st frame source [] raw [] [] []) row counter pref scratch := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;> by_cases h2 : k = st 2 <;>
    by_cases h3 : k = st 3 <;> by_cases h4 : k = st 4 <;> by_cases h5 : k = st 5 <;>
    simp_all [tapes, Write.tapes, Allocate.tapes, Function.update_apply, st.injective.eq_iff]

/-- The row outcome, with every literal/index/pref/scratch stack cleared. -/
def finished (st : Stacks K) (lab : Labels Λ) (b : Bool) (memory : τ)
    (frame : K → List Bool) (result : Option CellCodec.Cells) : Cfg K Λ (Bool × τ) :=
  match result with
  | none => cfg lab.writer.bad (b, memory) (tapes st frame [] [] [] [] [] [])
  | some row => cfg lab.writer.good (b, memory) (tapes st frame [] (CellCodec.encode row) [] [] [] [])

section Returning
variable (step : Cfg K Λ (Bool × τ) → Option (Cfg K Λ (Bool × τ)))
variable (st : Stacks K) (lab : Labels Λ) (exec : Executes step st lab)
variable (old : Bool) (memory : τ) (frame : K → List Bool)
include exec

theorem frame_exact (index : List Bool) (b : Bool) (row : List Bool) :
    RunsExactly step
      (cfg lab.scan (old, memory) (tapes st frame (Encoding.frame index ++ [b]) row [] [] [] []))
      (cfg lab.naturalMove (old, memory) (tapes st frame [b] row index [] [] []))
      (2 * (index.length + 1)) := by
  simpa only [← as_frame, Contract.frame_eq, List.append_nil] using
    Frame.extract_exact (st 0) (st 2) (st 5)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      step lab.scan lab.restore lab.naturalMove lab.writer.bad exec.scan exec.restore
      (old, memory) (tapes st frame [] row [] [] [] []) index [b] []

theorem natural_exact (index : List Bool) (b : Bool) (row : List Bool) :
    RunsExactly step
      (cfg lab.naturalMove (old, memory) (tapes st frame [b] row index [] [] []))
      (cfg lab.polarity (old, memory) (tapes st frame [b] row [] (encodeNat (decodeNat index)) [] []))
      (2 * index.length + 3) := by
  simpa only [← as_natural, naturalLabels, NaturalWords.canonicalize_eq, List.append_nil] using
    NaturalWords.canonicalize_exact step (naturalStacks st) (naturalLabels lab) exec.natural
      (old, memory) (tapes st frame [b] row [] [] [] []) index []

theorem polarity_step (b : Bool) (row counter : List Bool) :
    step (cfg lab.polarity (old, memory) (tapes st frame [b] row [] counter [] [])) =
      some (cfg lab.writer.loop (b, memory) (tapes st frame [] row [] counter [] [])) := by
  rw [cfg, exec.polarity]
  simp [polarityStmt, TM2.stepAux, cfg, tapes, st.injective.eq_iff]
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;> by_cases h2 : k = st 2 <;>
    by_cases h3 : k = st 3 <;> by_cases h4 : k = st 4 <;> by_cases h5 : k = st 5 <;>
    simp_all [Function.update_apply, st.injective.eq_iff]

/-- Full raw-literal execution, including a noncanonical natural word. The
caller-supplied Boolean register is replaced by the bit actually read. -/
theorem literal_returns (index : List Bool) (b : Bool) (row : CellCodec.Cells) :
    ∃ time : ℕ,
      time ≤ 4 * index.length + 9 + (row.length + 1) * (2 * (index.length + 1) + 6) ∧
      RunsExactly step
        (cfg lab.scan (old, memory)
          (tapes st frame (Encoding.frame index ++ [b]) (CellCodec.encode row) [] [] [] []))
        (finished st lab b memory frame (DenseNormalization.write (decodeNat index) b row).value) time := by
  have r1 := frame_exact step st lab exec old memory frame index b (CellCodec.encode row)
  have r2 := natural_exact step st lab exec old memory frame index b (CellCodec.encode row)
  have r3 := runsExactly_one (polarity_step step st lab exec old memory frame b (CellCodec.encode row)
    (encodeNat (decodeNat index)))
  obtain ⟨time, bound, run⟩ := Write.write_returns step (writeStacks st) lab.writer exec.writer
    b memory (tapes st frame [] [] [] [] [] []) row [] (decodeNat index)
  have writer : RunsExactly step
      (cfg lab.writer.loop (b, memory)
        (tapes st frame [] (CellCodec.encode row) [] (encodeNat (decodeNat index)) [] []))
      (finished st lab b memory frame (DenseNormalization.write (decodeNat index) b row).value) time := by
    have out : Write.finished (writeStacks st) lab.writer b memory (tapes st frame [] [] [] [] [] []) []
        (DenseNormalization.write (decodeNat index) b row).value =
        finished st lab b memory frame (DenseNormalization.write (decodeNat index) b row).value := by
      cases (DenseNormalization.write (decodeNat index) b row).value <;>
        simp only [Write.finished, finished, List.nil_append, ← as_writer]
    simpa only [out, CellCodec.encode_nil, List.reverse_nil, ← as_writer] using run
  refine ⟨time + (1 + ((2 * index.length + 3) + 2 * (index.length + 1))), ?_,
    ((r1.trans r2).trans r3).trans writer⟩
  have hl := (NaturalWords.canonicalize_length index).2
  rw [NaturalWords.canonicalize_eq] at hl
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at bound
  nlinarith

end Returning
end Counting.Algorithm.KarpLubyRequest.Dense.LiteralWrite
