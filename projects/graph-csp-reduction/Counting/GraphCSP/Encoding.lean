import Counting.GraphCSP.Model
import Counting.Encoding.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Independent faithful graph and CSP serializations

Graph words contain explicit indexed vertex declarations and ordered edge
records. CSP words contain an arbitrary ordered unary/binary occurrence list.
The two encoders are defined separately; only the later `encode_transform`
theorem connects them. Binary identifiers use the F1/mathlib little-endian
natural-number representation. The unary size header explicitly charges every
vertex, including isolated vertices. Both decoders are executable parsers.
-/

namespace Counting.GraphCSP

/-- Source syntax distinguishes vertex declarations from edge records. -/
inductive SourceSymbol where
  | count | header | vertex | edge | digit (b : Bool) | sep
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- Target syntax independently describes arbitrary constraint records. -/
inductive TargetSymbol where
  | count | header | unary | binary | digit (b : Bool) | sep
  deriving DecidableEq, Fintype, Inhabited, Repr

/-- The machine's finite symbol translation. -/
def symbolMap : SourceSymbol → TargetSymbol
  | .count => .count
  | .header => .header
  | .vertex => .unary
  | .edge => .binary
  | .digit b => .digit b
  | .sep => .sep

/-- A natural-valued record before bounds on its scopes are checked. -/
inductive RawConstraint where
  | unary (v : Nat)
  | binary (u v : Nat)
  deriving DecidableEq, Repr

namespace Constraint

def toRaw {n : Nat} : Constraint n → RawConstraint
  | .unary v => .unary v.val
  | .binary u v => .binary u.val v.val

end Constraint

namespace RawConstraint

/-- Checking scopes is part of decoding, not an assumption about arbitrary words. -/
def check (n : Nat) : RawConstraint → Option (Constraint n)
  | .unary v => if h : v < n then some (.unary ⟨v, h⟩) else none
  | .binary u v =>
    if hu : u < n then
      if hv : v < n then some (.binary ⟨u, hu⟩ ⟨v, hv⟩) else none
    else none

@[simp] theorem check_toRaw {n : Nat} (c : Constraint n) :
    c.toRaw.check n = some c := by
  cases c with
  | unary v => simp [Constraint.toRaw, check, v.isLt]
  | binary u v => simp [Constraint.toRaw, check, u.isLt, v.isLt]

end RawConstraint

/-- Binary digits terminated by a separator; identifiers are never unary. -/
def targetNat (n : Nat) : List TargetSymbol :=
  (Counting.Encoding.nat.encode n).map TargetSymbol.digit ++ [.sep]

def sourceNat (n : Nat) : List SourceSymbol :=
  (Counting.Encoding.nat.encode n).map SourceSymbol.digit ++ [.sep]

@[simp] theorem map_sourceNat (n : Nat) :
    (sourceNat n).map symbolMap = targetNat n := by
  simp [sourceNat, targetNat, List.map_map, Function.comp_def, symbolMap]

/-- Each record writes its ordered scope explicitly. -/
def targetRecord : RawConstraint → List TargetSymbol
  | .unary v => .unary :: targetNat v
  | .binary u v => .binary :: (targetNat u ++ targetNat v)

def sourceVertex (v : Nat) : List SourceSymbol := .vertex :: sourceNat v

def sourceEdge (u v : Nat) : List SourceSymbol :=
  .edge :: (sourceNat u ++ sourceNat v)

/-- Generic target record serialization, including unrestricted multiplicities. -/
def rawEncode (n : Nat) (cs : List RawConstraint) : List TargetSymbol :=
  List.replicate n .count ++ .header :: cs.flatMap targetRecord

/-- Independent encoder for every unary/binary CSP instance. -/
def cspEncode (I : CSP) : List TargetSymbol :=
  rawEncode I.n (I.constraints.map Constraint.toRaw)

/-- Explicit graph serialization: unary count, all binary vertex declarations,
then binary source/destination pairs in edge-occurrence order. -/
def graphEncode (G : Graph) : List SourceSymbol :=
  List.replicate G.n .count ++ .header ::
    ((List.finRange G.n).flatMap (fun v => sourceVertex v.val) ++
      G.edges.flatMap (fun e => sourceEdge e.1.val e.2.val))

/-- Read a delimited binary identifier without inspecting any later record. -/
def readDigits : List TargetSymbol → Option (List Bool × List TargetSymbol)
  | .sep :: xs => some ([], xs)
  | .digit b :: xs => do
    let (bs, rest) ← readDigits xs
    pure (b :: bs, rest)
  | _ => none

@[simp] theorem readDigits_word (bs : List Bool) (tail : List TargetSymbol) :
    readDigits (bs.map TargetSymbol.digit ++ .sep :: tail) = some (bs, tail) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [readDigits, ih]

def readNat (xs : List TargetSymbol) : Option (Nat × List TargetSymbol) := do
  let (bs, rest) ← readDigits xs
  pure (Computability.decodeNat bs, rest)

@[simp] theorem readNat_word (n : Nat) (tail : List TargetSymbol) :
    readNat (targetNat n ++ tail) = some (n, tail) := by
  simp [readNat, targetNat, List.append_assoc, Counting.Encoding.nat,
    Computability.decode_encodeNat]

/-- The unary header has its own terminator. -/
def readHeader : List TargetSymbol → Option (Nat × List TargetSymbol)
  | .header :: xs => some (0, xs)
  | .count :: xs => do
    let (n, rest) ← readHeader xs
    pure (n + 1, rest)
  | _ => none

@[simp] theorem readHeader_word (n : Nat) (tail : List TargetSymbol) :
    readHeader (List.replicate n .count ++ .header :: tail) = some (n, tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, readHeader, ih]

/-- Fuel bounds only the number of records; binary payloads are parsed directly. -/
def readRecords : Nat → List TargetSymbol → Option (List RawConstraint)
  | _, [] => some []
  | 0, _ :: _ => none
  | fuel + 1, .unary :: xs => do
    let (v, rest) ← readNat xs
    let cs ← readRecords fuel rest
    pure (.unary v :: cs)
  | fuel + 1, .binary :: xs => do
    let (u, rest) ← readNat xs
    let (v, rest) ← readNat rest
    let cs ← readRecords fuel rest
    pure (.binary u v :: cs)
  | _ + 1, _ => none

@[simp] theorem readRecords_word (cs : List RawConstraint) (fuel : Nat)
    (hf : cs.length ≤ fuel) :
    readRecords fuel (cs.flatMap targetRecord) = some cs := by
  induction cs generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons c cs ih =>
    cases fuel with
    | zero => simp at hf
    | succ fuel =>
      have hf' : cs.length ≤ fuel := by simpa using hf
      cases c with
      | unary v =>
        simp [targetRecord, readRecords, readNat_word, ih fuel hf']
      | binary u v =>
        simp [targetRecord, List.append_assoc, readRecords, readNat_word, ih fuel hf']

theorem records_length_le (cs : List RawConstraint) :
    cs.length ≤ (cs.flatMap targetRecord).length := by
  induction cs with
  | nil => simp
  | cons c cs ih => cases c <;> simp_all [targetRecord] <;> omega

/-- Parse all target records, rejecting malformed tags, out-of-bounds scopes,
and unterminated identifiers. Noncanonical binary digit strings are normalized. -/
def cspDecode (xs : List TargetSymbol) : Option CSP := do
  let (n, body) ← readHeader xs
  let cs ← readRecords body.length body
  let bounded ← cs.mapM (RawConstraint.check n)
  pure ⟨n, bounded⟩

@[simp] theorem check_map_toRaw {n : Nat} (cs : List (Constraint n)) :
    (cs.map Constraint.toRaw).mapM (RawConstraint.check n) = some cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [ih]

@[simp] theorem cspDecode_encode (I : CSP) : cspDecode (cspEncode I) = some I := by
  cases I with
  | mk n cs =>
    unfold cspDecode cspEncode rawEncode
    rw [readHeader_word]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [readRecords_word _ _ (records_length_le _)]
    simp only [Option.bind_some]
    rw [check_map_toRaw]
    rfl

/-- The two independently defined serializations are connected by a genuine
letter transformation that replaces declaration tags with constraint tags. -/
theorem encode_transform (G : Graph) :
    (graphEncode G).map symbolMap = cspEncode G.toCSP := by
  simp [graphEncode, cspEncode, rawEncode, Graph.toCSP, List.map_flatMap,
    List.flatMap_map, List.flatMap_append, List.map_map, Function.comp_def,
    sourceVertex, sourceEdge, targetRecord, Constraint.toRaw, symbolMap]

/-- Read only binary constraints as graph edges. -/
def onlyBinary {n : Nat} : Constraint n → Option (Fin n × Fin n)
  | .unary _ => none
  | .binary u v => some (u, v)

/-- A source word must contain exactly the canonical explicit vertex table.
The target parser itself places no such condition on arbitrary CSP instances. -/
def graphOfCSP (I : CSP) : Option Graph := do
  let edges ← (I.constraints.drop I.n).mapM onlyBinary
  let G : Graph := ⟨I.n, edges⟩
  if G.toCSP = I then pure G else none

@[simp] theorem onlyBinary_map {n : Nat} (es : List (Fin n × Fin n)) :
    (es.map (fun e => Constraint.binary e.1 e.2)).mapM onlyBinary = some es := by
  induction es with
  | nil => rfl
  | cons e es ih => simp [onlyBinary, ih]

@[simp] theorem graphOfCSP_toCSP (G : Graph) : graphOfCSP G.toCSP = some G := by
  cases G with
  | mk n es =>
    unfold graphOfCSP
    dsimp only [Graph.toCSP]
    rw [show ((List.finRange n).map Constraint.unary ++
      es.map (fun e => Constraint.binary e.1 e.2)).drop n =
      es.map (fun e => Constraint.binary e.1 e.2) by simp]
    rw [onlyBinary_map]
    simp

/-- Successful graph extraction certifies the entire canonical vertex table
and preserves every edge occurrence. -/
theorem graphOfCSP_sound {I : CSP} {G : Graph} (h : graphOfCSP I = some G) :
    G.toCSP = I := by
  unfold graphOfCSP at h
  cases he : (I.constraints.drop I.n).mapM onlyBinary with
  | none => simp [he] at h
  | some es =>
    rw [he] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    split at h
    next hi =>
      have hg : (⟨I.n, es⟩ : Graph) = G := Option.some.inj h
      simpa [hg] using hi
    next hi => simp at h

/-- The graph decoder checks the explicit vertex table after parsing. -/
def graphDecode (xs : List SourceSymbol) : Option Graph := do
  let I ← cspDecode (xs.map symbolMap)
  graphOfCSP I

@[simp] theorem graphDecode_encode (G : Graph) :
    graphDecode (graphEncode G) = some G := by
  simp [graphDecode, encode_transform]

/-- The letter machine is correct on every decoder-accepted source word,
including noncanonical binary digit strings accepted by the parser. -/
theorem decode_transform {xs : List SourceSymbol} {G : Graph}
    (h : graphDecode xs = some G) :
    cspDecode (xs.map symbolMap) = some G.toCSP := by
  unfold graphDecode at h
  cases hc : cspDecode (xs.map symbolMap) with
  | none => simp [hc] at h
  | some I =>
    rw [hc] at h
    simp only [Option.bind_eq_bind, Option.bind_some] at h
    rw [graphOfCSP_sound h]

/-- Faithful source encoding, with an executable decoder. -/
def graphEncoding : Computability.Encoding Graph SourceSymbol where
  encode := graphEncode
  decode := graphDecode
  decode_encode := graphDecode_encode

/-- Faithful target encoding for arbitrary occurrence lists. -/
def cspEncoding : Computability.Encoding CSP TargetSymbol where
  encode := cspEncode
  decode := cspDecode
  decode_encode := cspDecode_encode

/-- Every vertex is explicitly charged even before reading its binary declaration. -/
theorem vertices_le_graphEncode_length (G : Graph) : G.n ≤ (graphEncode G).length := by
  simp [graphEncode]

/-- Every target variable is explicitly charged even if no occurrence uses it. -/
theorem variables_le_cspEncode_length (I : CSP) : I.n ≤ (cspEncode I).length := by
  simp [cspEncode, rawEncode]

/-- Letter translation materializes exactly one output symbol per input symbol.
This size result is distinct from the machine's later transition-count proof. -/
theorem encode_transform_length (G : Graph) :
    (cspEncode G.toCSP).length = (graphEncode G).length := by
  rw [← encode_transform, List.length_map]

end Counting.GraphCSP
