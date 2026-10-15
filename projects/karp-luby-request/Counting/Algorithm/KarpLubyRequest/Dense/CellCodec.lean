import Counting.Algorithm.KarpLubyMachine.DenseNormalization

/-!
# Binary storage for materialized DNF rows

Every coordinate occupies exactly two symbols. The words `00`, `10`, and `11`
represent an unassigned, false, and true coordinate respectively. Row order and
multiplicity are retained by the original R1 framing operation. These definitions
specify stored words; they do not add decoding operations to machine control.
-/
namespace Counting.Algorithm.KarpLubyRequest.Dense.CellCodec
open Counting.Algorithm.KarpLuby
open Counting.Algorithm.KarpLubyMachine

abbrev Cells := DenseNormalization.Cells

def cell : Option Bool → List Bool
  | none => [false, false]
  | some b => [true, b]

def encode (xs : Cells) : List Bool := xs.flatMap cell

def decode : List Bool → Option Cells
  | [] => some []
  | false :: false :: rest => (decode rest).map (none :: ·)
  | true :: b :: rest => (decode rest).map (some b :: ·)
  | _ => none

@[simp] theorem encode_nil : encode [] = [] := rfl

@[simp] theorem encode_cons (x : Option Bool) (xs : Cells) :
    encode (x :: xs) = cell x ++ encode xs := rfl

@[simp] theorem decode_encode (xs : Cells) : decode (encode xs) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [encode_cons, cell, decode, ih]

theorem encode_injective : Function.Injective encode := by
  intro xs ys h
  have hd := congrArg decode h
  simpa only [decode_encode, Option.some.injEq] using hd

@[simp] theorem encode_length (xs : Cells) : (encode xs).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [encode_cons, cell, ih, Nat.mul_succ]

@[simp] theorem encode_append (xs ys : Cells) : encode (xs ++ ys) = encode xs ++ encode ys := by
  simp only [encode, List.flatMap_append]

/-- The actual allocator may emit zero pairs without inspecting unary bit values. -/
theorem encode_replicate_none (n : ℕ) :
    encode (List.replicate n none) = List.replicate (2 * n) false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, encode_cons, cell, ih]
    rw [Nat.mul_succ, Nat.add_comm (2 * n) 2, List.replicate_add]
    rfl

/-- Exact stored word for the canonical existing allocation function. -/
theorem encode_allocate (n : ℕ) :
    encode (DenseNormalization.allocate n).value = List.replicate (2 * n) false := by
  rw [DenseNormalization.allocate_value, encode_replicate_none]

/-- Rows are physically framed by the unique original R1 codec. The separate
binary row-count field is supplied by the eventual formula caller. -/
def rows (xs : List Cells) : List Bool := Encoding.frames (xs.map encode)

@[simp] theorem rows_nil : rows [] = [] := rfl

@[simp] theorem rows_cons (xs : Cells) (rest : List Cells) :
    rows (xs :: rest) = Encoding.frame (encode xs) ++ rows rest := rfl

/-- Fixed-width dense rows include coordinates of every unused variable. -/
theorem rows_length (xs : List Cells) (n : ℕ) (h : ∀ row ∈ xs, row.length = n) :
    (rows xs).length = xs.length * (4 * n + 1) := by
  induction xs with
  | nil => simp only [rows_nil, List.length_nil, Nat.zero_mul]
  | cons row rest ih =>
    have hr := h row (by simp)
    have ht := ih (fun r hm => h r (by simp [hm]))
    rw [rows_cons, List.length_append, Encoding.frame_length, encode_length, hr, ht,
      List.length_cons]
    simp only [Nat.add_mul, Nat.one_mul]
    omega

end Counting.Algorithm.KarpLubyRequest.Dense.CellCodec
