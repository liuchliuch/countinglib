import Holant.Complexity.Encoding
import Mathlib.Computability.Encoding
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega

/-!
# Explicit binary encodings

The codecs and framing proofs below are extracted from
`PlanarHom/Complexity.lean` at upstream commit
`db68e745380769c38c8347736d2d84fcde38263c`.
The upstream source and license metadata are recorded in `notes/encoding.md`.

The codewords and decoding behavior are preserved. The only structural change
is replacing the upstream duplicate `BitEncoding` structure by mathlib's current
`Computability.Encoding`. These are representation and bit-length results;
no polynomial-time implementation of the codecs is asserted by this module.
-/

namespace Counting.Encoding

/-- Finite binary words. -/
abbrev Bits := List Bool

/-- An explicit binary encoding with a checked decoding round trip.
Decoder validity, normalization, and running time are separate obligations. -/
abbrev BitEncoding (α : Type) := Computability.Encoding α Bool

/-- The checked decoding round trip makes every encoding injective. -/
theorem injective {α : Type} (e : BitEncoding α) : Function.Injective e.encode :=
  e.encode_injective

/-- Raw bit strings do not receive a second layer of encoding. -/
def bits : BitEncoding Bits := ⟨id, some, fun _ => rfl⟩

/-- Little-endian binary natural numbers, as supplied by mathlib. -/
def nat : BitEncoding ℕ where
  encode := Computability.encodeNat
  decode s := some (Computability.decodeNat s)
  decode_encode n := congrArg some (Computability.decode_encodeNat n)

/-- Unary size data, used for the number of explicitly present graph vertices.
Binary vertex counts alone would succinctly encode exponentially many isolated vertices. -/
def unaryNat : BitEncoding ℕ where
  encode := Computability.unaryEncodeNat
  decode s := some s.length
  decode_encode n := congrArg some (Computability.unary_decode_encode_nat n)

@[simp] theorem unaryNat_length (n : ℕ) : (unaryNat.encode n).length = n :=
  Computability.unary_decode_encode_nat n

/-- A bit is a single bit, not a unary natural. -/
def bool : BitEncoding Bool where
  encode b := [b]
  decode
    | [b] => some b
    | _ => none
  decode_encode _ := rfl

/-- Escape a word: every data bit is preceded by `true`, then `false` ends it. -/
def frame : Bits → Bits
  | [] => [false]
  | b :: bs => true :: b :: frame bs

/-- Read one escaped word and return its unconsumed suffix. -/
def unframe : Bits → Option (Bits × Bits)
  | false :: bs => some ([], bs)
  | true :: b :: bs => do
      let (word, rest) ← unframe bs
      return (b :: word, rest)
  | _ => none

@[simp] theorem unframe_frame_append (a b : Bits) :
    unframe (frame a ++ b) = some (a, b) := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [frame, unframe, ih]

@[simp] theorem frame_length (a : Bits) : (frame a).length = 2 * a.length + 1 := by
  induction a with
  | nil => rfl
  | cons x xs ih => simp [frame, ih]; omega

/-- A product is one framed first codeword followed by the second codeword. -/
def prod {α β : Type} (a : BitEncoding α) (b : BitEncoding β) :
    BitEncoding (α × β) where
  encode x := frame (a.encode x.1) ++ b.encode x.2
  decode s := do
    let (sa, sb) ← unframe s
    let xa ← a.decode sa
    let xb ← b.decode sb
    return (xa, xb)
  decode_encode x := by simp [unframe_frame_append, a.decode_encode, b.decode_encode]

@[simp] theorem prod_length {α β : Type} (a : BitEncoding α) (b : BitEncoding β)
    (x : α × β) :
    ((prod a b).encode x).length = 2 * (a.encode x.1).length +
      (b.encode x.2).length + 1 := by
  simp [prod]; omega

/-- A sequence of individually framed words, without its length header. -/
def frames : List Bits → Bits
  | [] => []
  | w :: ws => frame w ++ frames ws

/-- Escaping costs two bits per payload bit and one delimiter per word. -/
theorem frames_length (ws : List Bits) :
    (frames ws).length = 2 * (ws.map List.length).sum + ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [frames, ih]; omega

/-- Parse a specified finite number of words. The fuel is the encoded length. -/
def unframes : ℕ → Bits → Option (List Bits × Bits)
  | 0, s => some ([], s)
  | n + 1, s => do
      let (w, rest) ← unframe s
      let (ws, tail) ← unframes n rest
      return (w :: ws, tail)

@[simp] theorem unframes_frames_append (ws : List Bits) (tail : Bits) :
    unframes ws.length (frames ws ++ tail) = some (ws, tail) := by
  induction ws with
  | nil => rfl
  | cons w ws ih => simp [frames, unframes, List.append_assoc, ih]

@[simp] theorem unframes_frames (ws : List Bits) :
    unframes ws.length (frames ws) = some (ws, []) := by
  simpa using unframes_frames_append ws []

/-- Lists carry a binary length header; arbitrary long payloads are never atoms. -/
def list {α : Type} (a : BitEncoding α) : BitEncoding (List α) where
  encode xs := frame (nat.encode xs.length) ++ frames (xs.map a.encode)
  decode s := do
    let (size, rest) ← unframe s
    let n ← nat.decode size
    let (words, tail) ← unframes n rest
    if tail = [] then words.mapM a.decode else none
  decode_encode xs := by
    have hm : (xs.map a.encode).mapM a.decode = some xs := by
      induction xs with
      | nil => rfl
      | cons x xs ih => simp [List.map_cons, List.mapM_cons, a.decode_encode, ih]
    have h : unframes xs.length (frames (xs.map a.encode)) =
        some (xs.map a.encode, []) := by simpa using unframes_frames (xs.map a.encode)
    simpa [nat, h] using hm

/-- An explicit occurrence list cannot hide more items than its bit length. -/
theorem list_length_le {α : Type} (e : BitEncoding α) (xs : List α) :
    xs.length ≤ ((list e).encode xs).length := by
  simp only [list, List.length_append, frame_length, frames_length, List.length_map]
  omega

/-- A fixed coordinate vector is encoded as a list with its required length checked. -/
def vector {α : Type} (e : BitEncoding α) (n : ℕ) : BitEncoding (Fin n → α) where
  encode f := (list e).encode (List.ofFn f)
  decode s := do
    let xs ← (list e).decode s
    if h : xs.length = n then
      some (fun i => xs[i.val]'(by omega))
    else none
  decode_encode f := by simp [(list e).decode_encode]

/-- Transport an encoding along a concrete retract. No efficiency is asserted. -/
def retract {α β : Type} (e : BitEncoding β) (f : α → β) (g : β → α)
    (h : ∀ a, g (f a) = a) : BitEncoding α where
  encode a := e.encode (f a)
  decode s := (e.decode s).map g
  decode_encode a := by rw [e.decode_encode]; simp [h]

/-- Signed binary integers, using the two constructors of `Int`. -/
def int : BitEncoding ℤ :=
  retract (prod bool nat)
    (fun z => match z with
      | .ofNat n => (false, n)
      | .negSucc n => (true, n))
    (fun p => if p.1 then Int.negSucc p.2 else Int.ofNat p.2)
    (by intro z; cases z <;> rfl)

/-- Exact rationals are encoded by their reduced numerator and positive denominator.
The decoder normalizes even noncanonical input pairs. -/
def rat : BitEncoding ℚ :=
  retract (prod int nat) (fun q => (q.num, q.den))
    (fun p => mkRat p.1 p.2) Rat.mkRat_self


@[simp] theorem bits_length (s : Bits) : (bits.encode s).length = s.length := rfl

@[simp] theorem bool_length (b : Bool) : (bool.encode b).length = 1 := rfl

/-- The exact size of the binary list header and framed element payloads. -/
theorem list_length {α : Type} (e : BitEncoding α) (xs : List α) :
    ((list e).encode xs).length =
      2 * (nat.encode xs.length).length + 1 +
        (2 * ((xs.map e.encode).map List.length).sum + xs.length) := by
  simp only [list, List.length_append, frame_length, frames_length, List.length_map]

/-- Escaping is injective even before a decoder for the payload is chosen. -/
theorem frame_injective : Function.Injective frame := by
  intro a b h
  have hu := congrArg unframe h
  have ha : unframe (frame a) = some (a, []) := by
    simpa using unframe_frame_append a []
  have hb : unframe (frame b) = some (b, []) := by
    simpa using unframe_frame_append b []
  rw [ha, hb] at hu
  exact congrArg Prod.fst (Option.some.inj hu)

end Counting.Encoding
