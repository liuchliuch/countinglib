import Counting.Algorithm.KarpLubyRequest.Dense.CellCodec
import Holant.Complexity.BinaryArithmetic.Bits

/-!
# Stored-row sampling specification

The list specification exposes the physical order of every declared coordinate.
Only a free coordinate consumes a low bit of the rank word. These equations are
used to prove the finite scanner correct; they are not callbacks in its control.
-/
namespace Counting.Algorithm.KarpLubyRequest.Sampling.RowSemantics
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine
open Holant.Complexity Computability

abbrev Cells := DenseNormalization.Cells

def free : Cells → ℕ
  | [] => 0
  | none :: xs => free xs + 1
  | some _ :: xs => free xs

def sample : Cells → ℕ → List Bool
  | [], _ => []
  | none :: xs, r => (r % 2 == 1) :: sample xs (r / 2)
  | some b :: xs, r => b :: sample xs r

/-- The scanner's actual low-bit convention also specifies exhausted rank words. -/
def bits : Cells → List Bool → List Bool
  | [], _ => []
  | none :: xs, r => r.head?.getD false :: bits xs r.tail
  | some b :: xs, r => b :: bits xs r

@[simp] theorem free_le (xs : Cells) : free xs ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp only [free, List.length_cons] <;> omega

@[simp] theorem sample_length (xs : Cells) (r : ℕ) : (sample xs r).length = xs.length := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [sample, ih]

@[simp] theorem bits_length (xs : Cells) (r : List Bool) : (bits xs r).length = xs.length := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [bits, ih]

theorem low_bit (word : List Bool) :
    word.head?.getD false = (BinaryArithmetic.value word % 2 == 1) := by
  cases word with
  | nil => rfl
  | cons b rest => cases b <;> simp <;> omega

theorem tail_value (word : List Bool) :
    BinaryArithmetic.value word.tail = BinaryArithmetic.value word / 2 := by
  cases word with
  | nil => rfl
  | cons b rest => cases b <;> simp <;> omega

theorem bits_eq_sample (xs : Cells) (word : List Bool) :
    bits xs word = sample xs (BinaryArithmetic.value word) := by
  induction xs generalizing word with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | none => simp only [bits, sample, low_bit, ih, tail_value]
    | some b => simp only [bits, sample, ih]

@[simp] theorem bits_encodeNat (xs : Cells) (r : ℕ) :
    bits xs (encodeNat r) = sample xs r := by
  rw [bits_eq_sample, BinaryArithmetic.value_encodeNat]

theorem denote_cons_zero (x : Option Bool) (xs : Cells) :
    DenseNormalization.denote (xs.length + 1) (x :: xs) 0 = x := by
  cases x <;> rfl

theorem denote_cons_succ (x : Option Bool) (xs : Cells) :
    (fun i : Fin xs.length => DenseNormalization.denote (xs.length + 1) (x :: xs) i.succ) =
      DenseNormalization.denote xs.length xs := rfl

theorem free_denote (xs : Cells) :
    DNF.freeCount (DenseNormalization.denote xs.length xs) = free xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change DNF.freeCount (DenseNormalization.denote (xs.length + 1) (x :: xs)) = _
    dsimp only [DNF.freeCount]
    rw [denote_cons_zero, denote_cons_succ]
    cases x <;> simp only [free, ih]

/-- Exact original unranking, including explicit unused variables and zero rank. -/
theorem sample_denote (xs : Cells) (r : ℕ) :
    List.ofFn (DNF.sampleNat (DenseNormalization.denote xs.length xs) r) = sample xs r := by
  induction xs generalizing r with
  | nil => rfl
  | cons x xs ih =>
    change List.ofFn (DNF.sampleNat (DenseNormalization.denote (xs.length + 1) (x :: xs)) r) = _
    dsimp only [DNF.sampleNat]
    rw [denote_cons_zero, denote_cons_succ]
    cases x <;> simp only [sample, List.ofFn_cons, ih]

/-- The physical word machine therefore implements the unchanged original sampler. -/
theorem bits_original (xs : Cells) (r : ℕ) :
    bits xs (encodeNat r) =
      List.ofFn (DNF.sampleNat (DenseNormalization.denote xs.length xs) r) := by
  rw [bits_encodeNat, sample_denote]

end Counting.Algorithm.KarpLubyRequest.Sampling.RowSemantics
