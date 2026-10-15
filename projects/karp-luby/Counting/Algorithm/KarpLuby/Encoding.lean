import Counting.Algorithm.KarpLuby.DNF
import Mathlib.Computability.Encoding
import Mathlib.Algebra.Field.Rat
import Mathlib.Data.List.OfFn
import Lean.Elab.Tactic.Omega

/-!
# Binary boundary for the explicit DNF estimator

The codec primitives are a source-level extraction from the already checked
`Counting/Encoding/Basic.lean` in the sibling F1 foundations package; that source
ports `PlanarHom/Complexity.lean` at commit
`db68e745380769c38c8347736d2d84fcde38263c`. Codewords and primitive round-trip
proofs are preserved. The new dependent DNF input and checked-denominator output
codecs are specific to this package. No machine running-time claim is made here.
-/

namespace Counting.Algorithm.KarpLuby.Encoding

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

/-- The binary integer pair decoder rejects zero denominators. -/
def output : BitEncoding ℚ where
  encode q := (prod int nat).encode (q.num, q.den)
  decode s := do
    let (z, d) ← (prod int nat).decode s
    if d = 0 then none else some (mkRat z d)
  decode_encode q := by
    simp only [(prod int nat).decode_encode]
    simp [Nat.ne_of_gt q.pos, Rat.mkRat_self]

def encodeOutput (q : ℚ) : Bits := output.encode q

def decodeOutput (s : Bits) : Option ℚ := output.decode s

@[simp] theorem decode_encodeOutput (q : ℚ) :
    decodeOutput (encodeOutput q) = some q := output.decode_encode q

/-- Finite indices are stored in binary and their declared range is checked. -/
def literal (n : ℕ) : BitEncoding (Fin n × Bool) where
  encode l := (prod nat bool).encode (l.1.val, l.2)
  decode s := do
    let (i, b) ← (prod nat bool).decode s
    if h : i < n then some (⟨i, h⟩, b) else none
  decode_encode l := by simp [(prod nat bool).decode_encode, l.1.isLt]

/-- An explicit sequence of explicit literal occurrences. -/
def formula (n : ℕ) : BitEncoding (DNF.Formula n) := list (list (literal n))

/-- The variable count is part of the input, including isolated variables. -/
structure Input where
  variableCount : ℕ
  formula : DNF.Formula variableCount

/-- The framed unary header charges one bit per ambient variable before framing. -/
def input : BitEncoding Input where
  encode x := frame (unaryNat.encode x.variableCount) ++ (formula x.variableCount).encode x.formula
  decode s := do
    let (header, rest) ← unframe s
    let n ← unaryNat.decode header
    let f ← (formula n).decode rest
    return ⟨n, f⟩
  decode_encode x := by
    simp [unframe_frame_append, unaryNat.decode_encode, (formula x.variableCount).decode_encode]

def encodeInput (x : Input) : Bits := input.encode x

def decodeInput (s : Bits) : Option Input := input.decode s

@[simp] theorem decode_encodeInput (x : Input) :
    decodeInput (encodeInput x) = some x := input.decode_encode x

/-- The input cannot encode exponentially many isolated variables succinctly. -/
theorem variables_le_input_length (x : Input) : x.variableCount ≤ (encodeInput x).length := by
  simp only [encodeInput, input, List.length_append, frame_length, unaryNat_length]
  omega

theorem terms_le_input_length (x : Input) : x.formula.length ≤ (encodeInput x).length := by
  have h := list_length_le (list (literal x.variableCount)) x.formula
  simp only [encodeInput, input, List.length_append]
  exact h.trans (Nat.le_add_left _ _)

/-- Summed literal occurrences are also charged by the explicit list code. -/
theorem literals_le_input_length (x : Input) :
    (x.formula.map List.length).sum ≤ (encodeInput x).length := by
  have h : (x.formula.map List.length).sum ≤
      ((x.formula.map (list (literal x.variableCount)).encode).map List.length).sum := by
    induction x.formula with
    | nil => simp
    | cons t ts ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (list_length_le (literal x.variableCount) t) ih
  have he := list_length (list (literal x.variableCount)) x.formula
  change ((formula x.variableCount).encode x.formula).length = _ at he
  have hh : (x.formula.map List.length).sum ≤
      ((formula x.variableCount).encode x.formula).length := by omega
  simp only [encodeInput, input, List.length_append]
  exact hh.trans (Nat.le_add_left _ _)

/-- Every malformed variable index is rejected by the literal parser. -/
theorem literal_decode_out_of_range (n i : ℕ) (b : Bool) (hi : n ≤ i) :
    (literal n).decode ((prod nat bool).encode (i, b)) = none := by
  simp [literal, (prod nat bool).decode_encode, Nat.not_lt.mpr hi]

/-- A zero denominator is rejected rather than assigned a rational value. -/
theorem output_decode_zero_denominator (z : ℤ) :
    decodeOutput ((prod int nat).encode (z, 0)) = none := by
  simp [decodeOutput, output, (prod int nat).decode_encode]

/-- Exact binary output length in terms of numerator and denominator codewords. -/
theorem output_length (q : ℚ) :
    (encodeOutput q).length = 2 * (int.encode q.num).length +
      (nat.encode q.den).length + 1 := prod_length int nat (q.num, q.den)

/-- The inherited natural codec has exactly the standard binary bit length. -/
theorem nat_length (n : ℕ) : (nat.encode n).length = Nat.size n := by
  have hp (p : PosNum) : (Computability.encodePosNum p).length = p.natSize := by
    induction p with
    | one => rfl
    | bit0 p ih => simpa [Computability.encodePosNum, PosNum.natSize] using congrArg Nat.succ ih
    | bit1 p ih => simpa [Computability.encodePosNum, PosNum.natSize] using congrArg Nat.succ ih
  have hn (p : Num) : (Computability.encodeNum p).length = p.natSize := by
    cases p with
    | zero => rfl
    | pos p => exact hp p
  simpa only [nat, Computability.encodeNat, Num.natSize_to_nat, Num.to_of_nat] using hn (n : Num)

/-- The sign framing costs three bits, with negative predecessor coding no longer
than the binary magnitude. -/
theorem int_length_le (z : ℤ) : (int.encode z).length ≤ Nat.size z.natAbs + 3 := by
  cases z with
  | ofNat n =>
    change ((prod bool nat).encode (false, n)).length ≤ Nat.size n + 3
    rw [prod_length, bool_length, nat_length]
    dsimp only
    omega
  | negSucc n =>
    change ((prod bool nat).encode (true, n)).length ≤ Nat.size (n + 1) + 3
    rw [prod_length, bool_length, nat_length]
    dsimp only
    have h : Nat.size n ≤ Nat.size (n + 1) := Nat.size_le_size (by omega)
    omega

/-- The complete rational output has logarithmic magnitude/denominator length. -/
theorem output_length_le (q : ℚ) : (encodeOutput q).length ≤
    2 * Nat.size q.num.natAbs + Nat.size q.den + 7 := by
  rw [output_length, nat_length]
  have := int_length_le q.num
  omega

end Counting.Algorithm.KarpLuby.Encoding
