import Counting.Algorithm.KarpLubyRequest.CountedList

/-!
# Binary index comparison against a physical unary header

Every iteration consumes a real unary-header symbol before decrementing a
binary counter. A huge index therefore cannot cause a huge empty loop. Header
bit values are ignored, exactly as in R1's unary decoder. The caller supplies
an actual copy of that header; copying the original is a separate charged stage.
-/
namespace Counting.Algorithm.KarpLubyRequest.BoundedIndex

open Turing Computability
open Turing.TM2.Stmt
open Holant.Complexity StackProtocol IntegerArithmetic

variable {K Λ τ : Type} [DecidableEq K]
abbrev Stacks (K : Type) := Fin 3 ↪ K

structure Labels (Λ : Type) where
  loop : Λ
  borrow : Λ
  restore : Λ
  good : Λ
  bad : Λ

def checkStmt (unary counter : K) (borrow good bad : Λ) : Stmt K Λ τ :=
  pop unary (fun v b => (b, v.2))
    (branch (fun v => v.1.isSome)
      (peek counter (fun v b => (b, v.2))
        (branch (fun v => v.1.isSome)
          (load (fun v => (none, v.2)) (goto (fun _ => borrow)))
          (load (fun v => (none, v.2)) (goto (fun _ => good)))))
      (load (fun v => (none, v.2)) (goto (fun _ => bad))))

structure Executes (step : Cfg K Λ τ → Option (Cfg K Λ τ))
    (st : Stacks K) (lab : Labels Λ) : Prop where
  loop : ExecutesAt step lab.loop (checkStmt (st 0) (st 1) lab.borrow lab.good lab.bad)
  borrow : ExecutesAt step lab.borrow
    (CountedList.Counter.decrementStmt (st 1) (st 2) lab.borrow lab.restore)
  restore : ExecutesAt step lab.restore (copyMoveStmt (st 2) (st 1) lab.restore lab.loop)

def tapes (st : Stacks K) (frame : K → List Bool) (unary counter scratch : List Bool) :
    K → List Bool := tapes3 frame (st 0) (st 1) (st 2) unary counter scratch

private theorem counter_tapes (st : Stacks K) (frame : K → List Bool)
    (unary counter scratch : List Bool) :
    tapes st frame unary counter scratch = tapes3 frame (st 1) (st 0) (st 2) counter unary scratch := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;> by_cases h2 : k = st 2 <;>
    simp_all [tapes, tapes3, st.injective.eq_iff]

section Returning
variable (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (st : Stacks K) (lab : Labels Λ)
variable (exec : Executes step st lab) (memory : τ) (frame : K → List Bool)
include exec

theorem nil_step (counter : List Bool) :
    step (cfg lab.loop memory (tapes st frame [] counter [])) =
      some (cfg lab.bad memory (tapes st frame [] counter [])) := by
  rw [cfg, exec.loop]
  simp [checkStmt, TM2.stepAux, cfg, tapes, tapes3, st.injective.eq_iff]


theorem zero_step (bit : Bool) (tail : List Bool) :
    step (cfg lab.loop memory (tapes st frame (bit :: tail) [] [])) =
      some (cfg lab.good memory (tapes st frame tail [] [])) := by
  rw [cfg, exec.loop]
  simp [checkStmt, TM2.stepAux, cfg, tapes, tapes3, st.injective.eq_iff]
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;> by_cases h2 : k = st 2 <;>
    simp_all [Function.update_apply, st.injective.eq_iff]

theorem positive_step (bit : Bool) (tail counter : List Bool) (hc : counter ≠ []) :
    step (cfg lab.loop memory (tapes st frame (bit :: tail) counter [])) =
      some (cfg lab.borrow memory (tapes st frame tail counter [])) := by
  cases counter with
  | nil => contradiction
  | cons c counter =>
    rw [cfg, exec.loop]
    simp [checkStmt, TM2.stepAux, cfg, tapes, tapes3, st.injective.eq_iff]
    funext k
    by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;> by_cases h2 : k = st 2 <;>
      simp_all [Function.update_apply, st.injective.eq_iff]

theorem decrement_exact (unary counter : List Bool) :
    RunsExactly step (cfg lab.borrow memory (tapes st frame unary counter []))
      (cfg lab.loop memory (tapes st frame unary (decrement counter) []))
      (2 * (borrowCount counter + 1)) := by
  simpa only [counter_tapes] using
    CountedList.Counter.decrement_exact (st 1) (st 0) (st 2)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      (fun h => by have := st.injective h; contradiction)
      step lab.borrow lab.restore lab.loop exec.borrow memory frame exec.restore counter unary

/-- The physical token count, not the decoded binary index, drives induction and
bounds every accepting or rejecting execution. -/
theorem terminates (unary : List Bool) (n : ℕ) :
    ∃ (remaining counter : List Bool) (time : ℕ),
      time ≤ (unary.length + 1) * (2 * (encodeNat n).length + 3) ∧
      RunsExactly step (cfg lab.loop memory (tapes st frame unary (encodeNat n) []))
        (cfg (if n < unary.length then lab.good else lab.bad) memory
          (tapes st frame remaining counter [])) time ∧
      (n < unary.length → remaining = unary.drop (n + 1) ∧ counter = []) := by
  induction unary generalizing n with
  | nil =>
    refine ⟨[], encodeNat n, 1, by simp, ?_, by simp⟩
    simpa only [List.length_nil, Nat.not_lt_zero, ↓reduceIte] using
      runsExactly_one (nil_step step st lab exec memory frame (encodeNat n))
  | cons bit tail ih =>
    cases n with
    | zero =>
      refine ⟨tail, [], 1, by simp [show encodeNat 0 = [] from rfl] <;> omega, ?_, by simp⟩
      simpa only [List.length_cons, Nat.zero_lt_succ, ↓reduceIte, show encodeNat 0 = [] from rfl] using
        runsExactly_one (zero_step step st lab exec memory frame bit tail)
    | succ n =>
      have hc : encodeNat (n + 1) ≠ [] := by
        intro h
        have hz := congrArg decodeNat h
        rw [decode_encodeNat] at hz
        change n + 1 = 0 at hz
        omega
      obtain ⟨remaining, counter, time, ht, hr, hs⟩ := ih n
      have first := runsExactly_one (positive_step step st lab exec memory frame bit tail
        (encodeNat (n + 1)) hc)
      have dec := decrement_exact step st lab exec memory frame tail (encodeNat (n + 1))
      rw [decrement_encodeNat, Nat.add_sub_cancel] at dec
      have whole := (first.trans dec).trans hr
      refine ⟨remaining, counter, time + (2 * (borrowCount (encodeNat (n + 1)) + 1) + 1),
        ?_, ?_, ?_⟩
      · have hb := borrowCount_le (encodeNat (n + 1))
        have hl := decrement_length_le (encodeNat (n + 1))
        rw [decrement_encodeNat, Nat.add_sub_cancel] at hl
        simp only [List.length_cons]
        nlinarith
      · simpa only [List.length_cons, Nat.add_lt_add_iff_right] using whole
      · intro h
        have h' : n < tail.length := by simpa using h
        simpa only [List.drop_succ_cons] using hs h'

end Returning

end Counting.Algorithm.KarpLubyRequest.BoundedIndex
