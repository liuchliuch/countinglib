import Counting.Algorithm.KarpLubyRequest.StateAdapter
import Counting.Algorithm.KarpLuby.Dyadic
import Counting.Algorithm.KarpLuby.Encoding
import Holant.Complexity.BinaryArithmetic.Bits
import Holant.Complexity.GraphPreprocessing.Primitive

/-!
# A physical fixed-width fair-tape decoder

A physical clock word determines how many random bits are consumed. Its symbols
are irrelevant: the word can be a copy of the canonical total-mass word, whose
length is the cached dyadic width. Random bits are most-significant first, as in
R1's `decodeTape`. Leading zeroes are skipped by inspecting the output stack,
so the result is a canonical arithmetic word, not mathlib's noncanonical raw
natural codec. Every random/clock symbol is consumed by an actual pop.
-/
namespace Counting.Algorithm.KarpLubyRequest.FairTape
open Turing Computability Holant.Complexity StackProtocol GraphPreprocessing
open Counting.Algorithm.KarpLuby

abbrev Stack := Fin 3
abbrev State := Option Bool × Option Bool × Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Unit State

def tapes (clock random output : List Bool) : Stack → List Bool := ![clock, random, output]
def initial : State := (none, none, false)
def cfg (clock random output : List Bool) : Config := ⟨some (), initial, tapes clock random output⟩
def finished (success : Bool) (clock random output : List Bool) : Config :=
  ⟨none, (none, none, success), tapes clock random output⟩

def program (_ : Unit) : TM2.Stmt (fun _ : Stack => Bool) Unit State :=
  .pop 0 (fun v bit => (bit, v.2))
    (.branch (fun v => v.1.isSome)
      (.pop 1 (fun v bit => (bit, v.2))
        (.branch (fun v => v.1.isSome)
          (.peek 2 (fun v bit => (v.1, bit, false))
            (.branch (fun v => v.1.getD false || v.2.1.isSome)
              (.push 2 (fun v => v.1.getD false)
                (.load (fun _ => initial) (.goto (fun _ => ()))))
              (.load (fun _ => initial) (.goto (fun _ => ())))))
          (.load (fun _ => (none, none, false)) .halt)))
      (.load (fun _ => (none, none, true)) .halt))

abbrev computer : FinTM2 where
  K := Stack
  k₀ := 1
  k₁ := 2
  Γ _ := Bool
  Λ := Unit
  main := ()
  σ := State
  initialState := initial
  m := program

instance alphabetFintype (k : computer.K) : Fintype (computer.Γ k) := inferInstanceAs (Fintype Bool)

/-- Specification of a single physically implemented output update. -/
def advance (bit : Bool) (output : List Bool) : List Bool :=
  if output = [] ∧ bit = false then [] else bit :: output

/-- Accumulator for most-significant-first random tape, retaining no high zeros. -/
def collect : List Bool → List Bool → List Bool
  | [], output => output
  | bit :: rest, output => collect rest (advance bit output)

private theorem update_zero (clock random output word : List Bool) :
    Function.update (tapes clock random output) 0 word = tapes word random output := by
  funext k; fin_cases k <;> rfl
private theorem update_one (clock random output word : List Bool) :
    Function.update (tapes clock random output) 1 word = tapes clock word output := by
  funext k; fin_cases k <;> rfl
private theorem update_two (clock random output word : List Bool) :
    Function.update (tapes clock random output) 2 word = tapes clock random word := by
  funext k; fin_cases k <;> rfl

/-- One actual transition consumes one clock cell and one random bit. -/
theorem step_bit (tick bit : Bool) (clock random output : List Bool) :
    computer.step (cfg (tick :: clock) (bit :: random) output) =
      some (cfg clock random (advance bit output)) := by
  cases bit <;> cases output <;>
    simp [FinTM2.step, TM2.step, program, cfg, initial, advance, TM2.stepAux,
      update_zero, update_one, update_two, tapes]
  all_goals congr 2; funext k; fin_cases k <;> rfl

/-- Zero width succeeds without consuming even the first random bit. -/
theorem step_done (random output : List Bool) :
    computer.step (cfg [] random output) = some (finished true [] random output) := by
  simp [FinTM2.step, TM2.step, program, cfg, initial, finished, TM2.stepAux, update_zero, tapes]
  congr 2; funext k; fin_cases k <;> rfl

/-- A physically missing bit is rejected, with no padding supplied by a callback. -/
theorem step_short (tick : Bool) (clock output : List Bool) :
    computer.step (cfg (tick :: clock) [] output) = some (finished false clock [] output) := by
  simp [FinTM2.step, TM2.step, program, cfg, initial, finished, TM2.stepAux, update_zero, update_one, tapes]
  congr 2; funext k; fin_cases k <;> rfl

/-- Exactly the requested prefix is consumed; the random suffix is untouched. -/
theorem read_exact (bits clock suffix output : List Bool) (hlen : clock.length = bits.length) :
    (fun p => p.bind computer.step)^[bits.length + 1] (some (cfg clock (bits ++ suffix) output)) =
      some (finished true [] suffix (collect bits output)) := by
  induction bits generalizing clock output with
  | nil =>
    have hc : clock = [] := by simpa using hlen
    subst clock
    exact step_done suffix output
  | cons bit bits ih =>
    cases clock with
    | nil => simp at hlen
    | cons tick clock =>
      have hr := ih clock (advance bit output) (by simpa using hlen)
      simp only [List.cons_append, List.length_cons, collect]
      rw [Function.iterate_succ_apply]
      change (fun p => p.bind computer.step)^[bits.length + 1]
        (computer.step (cfg (tick :: clock) (bit :: (bits ++ suffix)) output)) = _
      rw [step_bit]
      exact hr

/-- A short random tape is detected at the first unavailable bit. Clock and
output stacks describe the actual consumed prefix, rather than a padded tape. -/
theorem read_short (bits clock output : List Bool) (hlen : bits.length < clock.length) :
    (fun p => p.bind computer.step)^[bits.length + 1] (some (cfg clock bits output)) =
      some (finished false (clock.drop (bits.length + 1)) [] (collect bits output)) := by
  induction bits generalizing clock output with
  | nil =>
    cases clock with
    | nil => simp at hlen
    | cons tick clock => exact step_short tick clock output
  | cons bit bits ih =>
    cases clock with
    | nil => simp at hlen
    | cons tick clock =>
      have hr := ih clock (advance bit output) (by simpa using hlen)
      simp only [List.length_cons, collect]
      rw [Function.iterate_succ_apply]
      change (fun p => p.bind computer.step)^[bits.length + 1]
        (computer.step (cfg (tick :: clock) (bit :: bits) output)) = _
      rw [step_bit]
      exact hr

/-- Total execution on arbitrary clock/random words. The exact transition
count is the physically inspected prefix plus one; surplus random bits remain. -/
theorem read_all (clock random output : List Bool) :
    (fun p => p.bind computer.step)^[min clock.length random.length + 1]
      (some (cfg clock random output)) =
      some (finished (decide (clock.length ≤ random.length))
        (clock.drop (random.length + 1)) (random.drop clock.length)
        (collect (random.take clock.length) output)) := by
  by_cases h : clock.length ≤ random.length
  · have hr := read_exact (random.take clock.length) clock (random.drop clock.length) output
      (by simp [List.length_take, Nat.min_eq_left h])
    have hc : clock.drop (random.length + 1) = [] := List.drop_eq_nil_of_le (by omega)
    simpa only [List.take_append_drop, List.length_take, Nat.min_eq_left h, decide_eq_true h, hc] using hr
  · have hr := read_short random clock output (by omega)
    have ht : random.take clock.length = random := List.take_of_length_le (by omega)
    have hd : random.drop clock.length = [] := List.drop_eq_nil_of_le (by omega)
    simpa only [Nat.min_eq_right (by omega : random.length ≤ clock.length), decide_eq_false h, ht, hd] using hr

theorem advance_value (bit : Bool) (output : List Bool) :
    BinaryArithmetic.value (advance bit output) = bit.toNat + 2 * BinaryArithmetic.value output := by
  cases output <;> cases bit <;> simp [advance]

theorem advance_canonical (bit : Bool) (output : List Bool) (h : BinaryArithmetic.Canonical output) :
    BinaryArithmetic.Canonical (advance bit output) := by
  cases output with
  | nil => cases bit <;> simp [advance, BinaryArithmetic.Canonical]
  | cons b rest => simpa [advance, BinaryArithmetic.Canonical] using h

theorem collect_canonical (bits output : List Bool) (h : BinaryArithmetic.Canonical output) :
    BinaryArithmetic.Canonical (collect bits output) := by
  induction bits generalizing output with
  | nil => exact h
  | cons bit bits ih => exact ih _ (advance_canonical bit output h)

/-- Ordinary positional value of an appended high word. -/
theorem value_append (a b : List Bool) :
    BinaryArithmetic.value (a ++ b) = BinaryArithmetic.value a + 2 ^ a.length * BinaryArithmetic.value b := by
  induction a with
  | nil => simp
  | cons bit a ih => simp only [List.cons_append, BinaryArithmetic.value_cons, List.length_cons, ih, pow_succ]; ring

theorem collect_value (bits output : List Bool) :
    BinaryArithmetic.value (collect bits output) =
      BinaryArithmetic.value bits.reverse + 2 ^ bits.length * BinaryArithmetic.value output := by
  induction bits generalizing output with
  | nil => simp [collect]
  | cons bit bits ih =>
    simp only [collect, ih, advance_value, List.reverse_cons, value_append, List.length_reverse,
      BinaryArithmetic.value_cons, BinaryArithmetic.value_nil, List.length_cons, pow_succ]
    ring

/-- The word delivered to arithmetic is canonical even when all tape bits are false. -/
theorem collect_encode (bits : List Bool) :
    collect bits [] = encodeNat (BinaryArithmetic.value bits.reverse) := by
  apply BinaryArithmetic.canonical_injective
  · exact collect_canonical bits [] trivial
  · exact BinaryArithmetic.canonical_encodeNat _
  · simp [collect_value, BinaryArithmetic.value_encodeNat]

/-- This positional value agrees with the original finite dyadic-tape decoder;
no arbitrary-word `Computability.decodeNat` is used for the random tape. -/
theorem value_ofFn (width : ℕ) (tape : CoinTape width) :
    BinaryArithmetic.value (List.ofFn tape).reverse = Counting.Algorithm.KarpLuby.decodeNat width tape := by
  induction width with
  | zero => simp
  | succ width ih =>
    rw [List.ofFn_succ, List.reverse_cons, value_append, List.length_reverse, List.length_ofFn,
      Counting.Algorithm.KarpLuby.decodeNat_succ]
    simp only [BinaryArithmetic.value_cons, BinaryArithmetic.value_nil, Nat.mul_zero, Nat.add_zero, ih]
    rfl

theorem read_coinTape (width : ℕ) (tape : CoinTape width) (clock suffix : List Bool)
    (hlen : clock.length = width) :
    (fun p => p.bind computer.step)^[width + 1]
      (some (cfg clock (List.ofFn tape ++ suffix) [])) =
      some (finished true [] suffix (encodeNat (Counting.Algorithm.KarpLuby.decodeNat width tape))) := by
  simpa only [List.length_ofFn, collect_encode, value_ofFn] using
    read_exact (List.ofFn tape) clock suffix [] (by simpa using hlen)

/-- A physical copy of the computed canonical mass word is exactly the dyadic
clock. The actual decoder takes that word, rather than recomputing mass/width. -/
theorem read_massClock (mass : ℕ) (tape : CoinTape (dyadicBits mass)) (suffix : List Bool) :
    (fun p => p.bind computer.step)^[dyadicBits mass + 1]
      (some (cfg (encodeNat mass) (List.ofFn tape ++ suffix) [])) =
      some (finished true [] suffix
        (encodeNat (Counting.Algorithm.KarpLuby.decodeNat (dyadicBits mass) tape))) := by
  apply read_coinTape
  change (encodeNat mass).length = Nat.size mass
  exact Encoding.nat_length mass

theorem statement_budget (label : Unit) : TM2Cost.budget (program label) ≤ 9 := by
  cases label; decide

/-- The instruction accumulator instruments precisely the same total physical
execution, including a rejecting short-tape run and the final halt. -/
theorem bit_cost (clock random : List Bool) :
    (Primitive.run program (min clock.length random.length + 1) (some (cfg clock random []))).2 =
      some (finished (decide (clock.length ≤ random.length))
        (clock.drop (random.length + 1)) (random.drop clock.length)
        (encodeNat (BinaryArithmetic.value (random.take clock.length).reverse))) ∧
    (Primitive.run program (min clock.length random.length + 1) (some (cfg clock random []))).1 ≤
      9 * (clock.length + 1) := by
  have hr := read_all clock random []
  rw [collect_encode] at hr
  have hc := Primitive.execution_cost program 9 statement_budget _ _ _ hr
  exact ⟨hc.1, hc.2.trans (Nat.mul_le_mul_left 9 (by omega))⟩

end Counting.Algorithm.KarpLubyRequest.FairTape
