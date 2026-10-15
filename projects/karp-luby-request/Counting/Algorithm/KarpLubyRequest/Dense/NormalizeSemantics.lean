import Counting.Algorithm.KarpLubyRequest.Dense.CellCodec
import Counting.Algorithm.KarpLubyRequest.LiteralFields

/-!
# Exact semantic bridge for the physical tail-first traversal

These functions describe stored words and machine outcomes, not running time.
The actual program reverses the framed list before traversing it, so no
commutation or permutation assumption about literals is required.
-/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Normalize
open Computability
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

abbrev RawLiteral := List Bool × Bool

def literalWord (l : RawLiteral) : List Bool := Encoding.frame l.1 ++ [l.2]
def literalValue (l : RawLiteral) : ℕ × Bool := (decodeNat l.1, l.2)

def writes : List (ℕ × Bool) → Option CellCodec.Cells → Option CellCodec.Cells
  | [], row => row
  | l :: rest, row => writes rest (row.bind (fun xs => (DenseNormalization.write l.1 l.2 xs).value))

@[simp] theorem writes_nil (row : Option CellCodec.Cells) : writes [] row = row := rfl

@[simp] theorem writes_none (ls : List (ℕ × Bool)) : writes ls none = none := by
  induction ls <;> simp [writes, *]

theorem writes_append (a b : List (ℕ × Bool)) (row : Option CellCodec.Cells) :
    writes (a ++ b) row = writes b (writes a row) := by
  induction a generalizing row with
  | nil => rfl
  | cons l a ih => simp only [List.cons_append, writes, ih]

/-- The canonical tail-first algorithm is exactly forward writing of the
reversed occurrence list, including early failure on a conflicting suffix. -/
theorem writes_reverse_normalize {n : ℕ} (t : DNF.RawTerm n) :
    writes ((t.map (fun l => (l.1.val, l.2))).reverse)
      (some (DenseNormalization.allocate n).value) = (DenseNormalization.normalize n t).value := by
  induction t with
  | nil => rfl
  | cons l t ih =>
    rw [List.map_cons, List.reverse_cons, writes_append, ih]
    cases h : (DenseNormalization.normalize n t).value <;>
      simp [writes, DenseNormalization.normalize, h]

/-- A raw index may be noncanonical. Its decoded value, rather than its word,
selects the coordinate written by the finite program. -/
def rawWrites (words : List RawLiteral) (row : Option CellCodec.Cells) : Option CellCodec.Cells :=
  writes (words.map literalValue) row

theorem rawWrites_normalize {n : ℕ} (t : DNF.RawTerm n) (words : List RawLiteral)
    (h : words.map literalValue = t.map (fun l => (l.1.val, l.2))) :
    rawWrites words.reverse (some (DenseNormalization.allocate n).value) =
      (DenseNormalization.normalize n t).value := by
  rw [rawWrites, List.map_reverse, h, writes_reverse_normalize]

private theorem bool_decode_some (bits : List Bool) (b : Bool)
    (h : Encoding.bool.decode bits = some b) : bits = [b] := by
  rw [RationalFields.bool_decode] at h
  cases bits with
  | nil => cases h
  | cons bit rest =>
    cases rest with
    | nil =>
      have hb : bit = b := Option.some.inj h
      subst bit
      rfl
    | cons x rest => cases h

/-- Every accepted literal, including raw noncanonical index words, has the
physical shape consumed by `LiteralWrite.literal_returns`. -/
theorem literal_parts {n : ℕ} (raw : List Bool) (l : Fin n × Bool)
    (h : (Encoding.literal n).decode raw = some l) :
    ∃ index : List Bool, raw = literalWord (index, l.2) ∧ decodeNat index = l.1.val := by
  have hh := congrArg (Option.map (fun p : Fin n × Bool => (p.1.val, p.2))) h
  rw [LiteralFields.literal_decode_eq] at hh
  cases hs : LiteralFields.separate n raw with
  | none => simp [hs] at hh
  | some f =>
    have hp : (decodeNat f.index, f.polarity) = (l.1.val, l.2) := by simpa only [hs, Option.map_some, Option.some.injEq] using hh
    have hp1 := congrArg Prod.fst hp
    have hp2 := congrArg Prod.snd hp
    cases hu : Encoding.unframe raw with
    | none => simp [LiteralFields.separate, hu] at hs
    | some p =>
      rcases p with ⟨index, sign⟩
      cases hb : Encoding.bool.decode sign with
      | none => simp [LiteralFields.separate, hu, hb] at hs
      | some bit =>
        by_cases hi : decodeNat index < n
        · simp [LiteralFields.separate, hu, hb, hi] at hs
          subst f
          change bit = l.2 at hp2
          have hsign := bool_decode_some sign bit hb
          have hraw : raw = Encoding.frame index ++ sign := by
            rw [Contract.unframe_eq] at hu
            simpa only [Contract.frame_eq] using
              (Holant.Complexity.GraphPreprocessing.Frame.unframe_some_iff raw index sign).mp hu
          refine ⟨index, ?_, hp1⟩
          simpa only [literalWord, hsign, hp2] using hraw
        · simp [LiteralFields.separate, hu, hb, hi] at hs

end Counting.Algorithm.KarpLubyRequest.Dense.Normalize
