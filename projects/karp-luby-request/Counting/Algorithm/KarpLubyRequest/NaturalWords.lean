import Counting.Algorithm.KarpLubyRequest.Contract
import Mathlib.Tactic.FinCases
import Mathlib.Data.Fin.VecNotation

/-!
# Canonicalizing the exact raw natural-number codec

Mathlib's `decodeNat` is total but is not ordinary positional evaluation on
arbitrary words. A nonempty word ending in `false` receives an implicit high
`true`; a word ending in `true` is already canonical. The program below realizes
exactly `encodeNat (decodeNat raw)` on every raw word. It uses the canonical H1
copy loops, one finite highest-bit test, and three Boolean stacks. No natural
number is stored in finite control or evaluated by a transition.
-/
namespace Counting.Algorithm.KarpLubyRequest.NaturalWords

open Turing Computability
open Turing.TM2.Stmt
open Holant.Complexity StackProtocol

/-- Positive decoding adds the implicit high bit only at an empty positive tail.
This is a specification, not a machine instruction. -/
def positive (raw : List Bool) : List Bool := encodePosNum (decodePosNum raw)

@[simp] theorem positive_nil : positive [] = [true] := rfl
@[simp] theorem positive_false (rest : List Bool) :
    positive (false :: rest) = false :: positive rest := rfl
@[simp] theorem positive_true (rest : List Bool) :
    positive (true :: rest) = if rest = [] then [true] else true :: positive rest := by
  change encodePosNum (if rest = [] then PosNum.one else PosNum.bit1 (decodePosNum rest)) = _
  by_cases h : rest = [] <;> simp [h, encodePosNum, positive]

/-- The empty natural word represents zero, unlike the empty positive tail. -/
def canonicalize (raw : List Bool) : List Bool :=
  if raw = [] then [] else positive raw

theorem positive_eq (raw : List Bool) :
    positive raw = encodePosNum (decodePosNum raw) := rfl

/-- Exact compatibility with the locked decoder, including noncanonical words. -/
theorem canonicalize_eq (raw : List Bool) :
    canonicalize raw = encodeNat (decodeNat raw) := by
  change canonicalize raw = encodeNum ((decodeNum raw : ℕ) : Num)
  rw [Num.of_to_nat]
  by_cases he : raw = []
  · subst raw; rfl
  · dsimp only [canonicalize, decodeNum]
    rw [if_neg he]
    simp only [PosNum.cast_to_num, ite_eq_right he]
    rfl

@[simp] theorem positive_append_false (pre : List Bool) :
    positive (pre ++ [false]) = pre ++ [false, true] := by
  induction pre with
  | nil => rfl
  | cons bit pre ih => cases bit <;> simp [ih]

@[simp] theorem positive_append_true (pre : List Bool) :
    positive (pre ++ [true]) = pre ++ [true] := by
  induction pre with
  | nil => rfl
  | cons bit pre ih => cases bit <;> simp [ih]

@[simp] theorem canonicalize_nil : canonicalize [] = [] := rfl

@[simp] theorem canonicalize_append_false (pre : List Bool) :
    canonicalize (pre ++ [false]) = pre ++ [false, true] := by
  simp [canonicalize]

@[simp] theorem canonicalize_append_true (pre : List Bool) :
    canonicalize (pre ++ [true]) = pre ++ [true] := by
  simp [canonicalize]

theorem canonicalize_length (raw : List Bool) :
    raw.length ≤ (canonicalize raw).length ∧ (canonicalize raw).length ≤ raw.length + 1 := by
  induction raw using List.reverseRecOn with
  | nil => simp
  | append_singleton pre bit ih => cases bit <;> simp

@[simp] theorem decode_canonicalize (raw : List Bool) :
    decodeNat (canonicalize raw) = decodeNat raw := by
  rw [canonicalize_eq, decode_encodeNat]

@[simp] theorem canonicalize_encode (n : ℕ) : canonicalize (encodeNat n) = encodeNat n := by
  rw [canonicalize_eq, decode_encodeNat]

variable {K Λ τ : Type} [DecidableEq K]

/-- Inspect the highest original bit without consuming it. An implicit high one
is prepended to the destination exactly when this bit is false. -/
def highestStmt (tmp dst : K) (restore : Λ) : Stmt K Λ τ :=
  peek tmp (fun v bit => (bit, v.2))
    (branch (fun v => v.1.isSome && !v.1.getD false)
      (push dst (fun _ => true)
        (load (fun v => (none, v.2)) (goto (fun _ => restore))))
      (load (fun v => (none, v.2)) (goto (fun _ => restore))))

omit [DecidableEq K] in
theorem highestStmt_budget (tmp dst : K) (restore : Λ) :
    TM2Cost.budget (highestStmt (τ := τ) tmp dst restore) = 5 := rfl

structure Labels (Λ : Type) where
  move : Λ
  highest : Λ
  restore : Λ
  next : Λ

/-- Source is consumed; canonical output is prepended to destination. -/
abbrev Stacks (K : Type) := Fin 3 ↪ K

def tapes (st : Stacks K) (frame : K → List Bool)
    (source destination temporary : List Bool) : K → List Bool :=
  tapes3 frame (st 0) (st 1) (st 2) source destination temporary

@[simp] theorem tapes_at (st : Stacks K) (frame : K → List Bool)
    (source destination temporary : List Bool) (i : Fin 3) :
    tapes st frame source destination temporary (st i) =
      (![source, destination, temporary] : Fin 3 → List Bool) i := by
  fin_cases i <;> simp [tapes, tapes3, st.injective.eq_iff]

theorem tapes_other (st : Stacks K) (frame : K → List Bool)
    (source destination temporary : List Bool) (k : K)
    (h : ∀ i : Fin 3, k ≠ st i) :
    tapes st frame source destination temporary k = frame k := by
  simp [tapes, tapes3, h]

structure Executes (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (st : Stacks K) (lab : Labels Λ) : Prop where
  move : ExecutesAt step lab.move (copyMoveStmt (st 0) (st 2) lab.move lab.highest)
  highest : ExecutesAt step lab.highest (highestStmt (st 2) (st 1) lab.restore)
  restore : ExecutesAt step lab.restore (copyMoveStmt (st 2) (st 1) lab.restore lab.next)

private theorem tapes_restore (st : Stacks K) (frame : K → List Bool)
    (source destination temporary : List Bool) :
    tapes st frame source destination temporary =
      tapes3 frame (st 2) (st 0) (st 1) temporary source destination := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;> by_cases h2 : k = st 2 <;>
    simp_all [tapes, tapes3, st.injective.eq_iff]

section Returning
variable (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (st : Stacks K) (lab : Labels Λ)
variable (exec : Executes step st lab) (memory : τ) (frame : K → List Bool)

include exec

theorem move_exact (raw output : List Bool) :
    RunsExactly step (cfg lab.move memory (tapes st frame raw output []))
      (cfg lab.highest memory (tapes st frame [] output raw.reverse)) (raw.length + 1) := by
  simpa only [tapes, List.append_nil] using
    copy_move_exact (st 0) (st 1) (st 2)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      step lab.move lab.highest exec.move memory frame raw output []

theorem highest_step (temporary output : List Bool) :
    step (cfg lab.highest memory (tapes st frame [] output temporary)) =
      some (cfg lab.restore memory
        (tapes st frame [] (if temporary.head? = some false then true :: output else output) temporary)) := by
  rw [cfg, exec.highest]
  cases temporary with
  | nil => simp [highestStmt, TM2.stepAux, cfg, tapes, tapes3, st.injective.eq_iff]
  | cons bit rest =>
    cases bit <;> simp [highestStmt, TM2.stepAux, cfg, tapes, tapes3, st.injective.eq_iff,
      update_tapes3_dst]
    funext k
    by_cases h1 : k = st 1 <;> by_cases h2 : k = st 2 <;>
      simp_all [Function.update_apply, st.injective.eq_iff]

theorem restore_exact (temporary output : List Bool) :
    RunsExactly step (cfg lab.restore memory (tapes st frame [] output temporary))
      (cfg lab.next memory (tapes st frame [] (temporary.reverse ++ output) []))
      (temporary.length + 1) := by
  simpa only [tapes_restore] using
    copy_move_exact (st 2) (st 0) (st 1)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      step lab.restore lab.next exec.restore memory frame temporary [] output

/-- A real returning execution on every raw word, with caller memory and all
unselected stacks preserved. The bound is exact and independent of decoded value. -/
theorem canonicalize_exact (raw output : List Bool) :
    RunsExactly step (cfg lab.move memory (tapes st frame raw output []))
      (cfg lab.next memory (tapes st frame [] (encodeNat (decodeNat raw) ++ output) []))
      (2 * raw.length + 3) := by
  have hm := move_exact step st lab exec memory frame raw output
  have hh := runsExactly_one (highest_step step st lab exec memory frame raw.reverse output)
  have hr := restore_exact step st lab exec memory frame raw.reverse
    (if raw.reverse.head? = some false then true :: output else output)
  have run := (hm.trans hh).trans hr
  have he : raw.reverse.reverse ++
      (if raw.reverse.head? = some false then true :: output else output) =
      canonicalize raw ++ output := by
    induction raw using List.reverseRecOn with
    | nil => simp
    | append_singleton pre bit ih =>
      cases bit <;> simp [List.reverse_append, List.append_assoc]
  rw [he, canonicalize_eq] at run
  convert run using 1 <;> simp only [List.length_reverse] <;> omega

end Returning

/-- A concrete finite standalone instance. -/
def localStacks : Stacks (Fin 3) := ⟨id, fun _ _ h => h⟩
def localLabels : Labels (Fin 4) := ⟨0, 1, 2, 3⟩

def program (label : Fin 4) : Stmt (Fin 3) (Fin 4) Unit :=
  if label = 0 then copyMoveStmt 0 2 0 1
  else if label = 1 then highestStmt 2 1 2
  else if label = 2 then copyMoveStmt 2 1 2 3
  else halt

abbrev computer : FinTM2 where
  K := Fin 3
  k₀ := 0
  k₁ := 1
  Γ _ := Bool
  Λ := Fin 4
  main := 0
  σ := Option Bool × Unit
  initialState := (none, ())
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) :=
  inferInstanceAs (Fintype Bool)

theorem statement_budget (label : Fin 4) : TM2Cost.budget (program label) ≤ 5 := by
  fin_cases label <;> decide

theorem computer_executes : Executes computer.step localStacks localLabels := by
  constructor <;> intro state tape <;> rfl

theorem cfg_init (raw : List Bool) :
    cfg (0 : Fin 4) () (tapes localStacks (fun _ => []) raw [] []) = initList computer raw := by
  unfold cfg initList
  congr 1
  funext k
  fin_cases k <;> rfl

/-- Every raw word actually reaches the canonical-word return configuration. -/
theorem computer_returns (raw : List Bool) :
    RunsExactly computer.step (initList computer raw)
      (cfg (3 : Fin 4) () (tapes localStacks (fun _ => []) [] (encodeNat (decodeNat raw)) []))
      (2 * raw.length + 3) := by
  simpa only [localLabels, cfg_init, List.append_nil] using
    canonicalize_exact computer.step localStacks localLabels computer_executes () (fun _ => []) raw []

theorem return_halts (output : List Bool) :
    computer.step (cfg (3 : Fin 4) () (tapes localStacks (fun _ => []) [] output [])) =
      some (haltList computer output) := by
  unfold haltList
  dsimp [FinTM2.step, TM2.step, computer, program, cfg, TM2.stepAux]
  congr 2
  funext k
  fin_cases k <;> rfl

/-- Clean all-input halting with canonical output and exact linear step count. -/
theorem computer_halts (raw : List Bool) :
    RunsExactly computer.step (initList computer raw)
      (haltList computer (encodeNat (decodeNat raw))) (2 * raw.length + 4) := by
  convert (computer_returns raw).trans
    (runsExactly_one (return_halts (encodeNat (decodeNat raw)))) using 1 <;> omega

end Counting.Algorithm.KarpLubyRequest.NaturalWords
