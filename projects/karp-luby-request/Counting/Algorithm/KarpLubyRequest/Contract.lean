import Counting.Algorithm.KarpLubyMachine.RequestProgram
import Holant.Complexity.GraphPreprocessing.Frame

/-!
# The unchanged raw request grammar and machine handoff

The first three framed payloads are the problem, accuracy, and confidence;
the remainder is the finite fair-bit tape. Splitting those fields does not yet
validate their inner codecs. This module proves that splitting and subsequently
validating them recovers exactly R1's total decoder, including malformed inputs.
-/
namespace Counting.Algorithm.KarpLubyRequest.Contract

open Counting.Algorithm.KarpLuby

structure Fields where
  problem : List Bool
  epsilon : List Bool
  delta : List Bool
  tape : List Bool
  deriving DecidableEq

/-- Three framing calls preserve the entire unconsumed tape. -/
def split (raw : List Bool) : Option Fields := do
  let (p, rest) ← Encoding.unframe raw
  let (e, rest) ← Encoding.unframe rest
  let (d, tape) ← Encoding.unframe rest
  return ⟨p, e, d, tape⟩

/-- Inner validation retains the existing dependent variable range checks and
rational denominator tests; no new canonical-representation restriction is added. -/
def validate (fields : Fields) : Option ProgramEncoding.Request := do
  let p ← Encoding.input.decode fields.problem
  let e ← Encoding.output.decode fields.epsilon
  let d ← Encoding.output.decode fields.delta
  return ⟨p, e, d, fields.tape⟩

def decode (raw : List Bool) : Option ProgramEncoding.Request := (split raw).bind validate

theorem decode_eq (raw : List Bool) : decode raw = ProgramEncoding.request.decode raw := by
  dsimp only [ProgramEncoding.request, Encoding.retract, Encoding.bits]
  cases hp : Encoding.unframe raw with
  | none => simp [decode, split, Encoding.prod, hp]
  | some p =>
    rcases p with ⟨p, rest⟩
    cases he : Encoding.unframe rest with
    | none =>
      cases Encoding.input.decode p <;>
        simp [decode, split, Encoding.prod, hp, he]
    | some e =>
      rcases e with ⟨e, rest⟩
      cases hd : Encoding.unframe rest with
      | none =>
        cases Encoding.input.decode p <;> cases Encoding.output.decode e <;>
          simp [decode, split, Encoding.prod, hp, he, hd]
      | some d =>
        rcases d with ⟨d, tape⟩
        cases hdp : Encoding.input.decode p <;> cases hde : Encoding.output.decode e <;>
          cases hdd : Encoding.output.decode d <;>
          simp [decode, split, validate, Encoding.prod, hp, he, hd, hdp, hde, hdd]

def join (f : Fields) : List Bool :=
  Encoding.frame f.problem ++ Encoding.frame f.epsilon ++ Encoding.frame f.delta ++ f.tape

@[simp] theorem split_join (f : Fields) : split (join f) = some f := by
  cases f
  simp [split, join, List.append_assoc]

def encodedFields (r : ProgramEncoding.Request) : Fields :=
  ⟨Encoding.input.encode r.problem, Encoding.output.encode r.epsilon,
    Encoding.output.encode r.delta, r.tape⟩

theorem request_encode (r : ProgramEncoding.Request) :
    ProgramEncoding.request.encode r = join (encodedFields r) := by
  dsimp only [ProgramEncoding.request, Encoding.retract, Encoding.bits]
  simp [Encoding.prod,
    join, encodedFields, List.append_assoc]

@[simp] theorem split_request (r : ProgramEncoding.Request) :
    split (ProgramEncoding.request.encode r) = some (encodedFields r) := by
  rw [request_encode, split_join]

@[simp] theorem validate_encodedFields (r : ProgramEncoding.Request) :
    validate (encodedFields r) = some r := by
  cases r
  simp [validate, encodedFields, Encoding.input.decode_encode, Encoding.output.decode_encode]

/-- The whole machine must eventually realize this exact composition. This is a
semantic equality, not an assumed machine or running-time certificate. -/
theorem evalBits_eq (raw : List Bool) : ProgramEncoding.evalBits raw =
    Encoding.encodeOutput (match (split raw).bind validate with
      | none => 0
      | some r => KarpLubyMachine.RequestProgram.evalRequest r |>.value) := by
  rw [← decode, decode_eq]
  simp only [ProgramEncoding.evalBits, KarpLubyMachine.RequestProgram.evalRequest_value]
  rfl

/-- The canonical H1 returning frame routine implements the same bit grammar. -/
theorem frame_eq (word : List Bool) : Encoding.frame word = Holant.Algebraic.frame word := by
  induction word with
  | nil => rfl
  | cons b word ih => simpa only [Encoding.frame, Holant.Algebraic.frame, Function.comp_apply] using congrArg (List.cons true ∘ List.cons b) ih

theorem unframe_eq (word : List Bool) : Encoding.unframe word = Holant.Algebraic.unframe word := by
  match word with
  | [] => rfl
  | false :: _ => rfl
  | [true] => rfl
  | true :: b :: rest =>
    simp only [Encoding.unframe, Holant.Algebraic.unframe, unframe_eq rest]
    cases Holant.Algebraic.unframe rest <;> rfl
termination_by word.length

/-- Successful splitting reconstructs the exact original raw word, without
assuming canonical inner encodings. -/
theorem split_some_raw {raw : List Bool} {f : Fields} (h : split raw = some f) :
    raw = join f := by
  unfold split at h
  cases hp : Encoding.unframe raw with
  | none => simp [hp] at h
  | some p =>
    rcases p with ⟨p, rest⟩
    cases he : Encoding.unframe rest with
    | none => simp [hp, he] at h
    | some e =>
      rcases e with ⟨e, rest⟩
      cases hd : Encoding.unframe rest with
      | none => simp [hp, he, hd] at h
      | some d =>
        rcases d with ⟨d, tape⟩
        simp [hp, he, hd] at h
        subst f
        rw [unframe_eq] at hp he hd
        rw [(Holant.Complexity.GraphPreprocessing.Frame.unframe_some_iff _ _ _).mp hp,
          (Holant.Complexity.GraphPreprocessing.Frame.unframe_some_iff _ _ _).mp he,
          (Holant.Complexity.GraphPreprocessing.Frame.unframe_some_iff _ _ _).mp hd]
        simp [join, frame_eq, List.append_assoc]

theorem split_some_iff (raw : List Bool) (f : Fields) :
    split raw = some f ↔ raw = join f := by
  constructor
  · exact split_some_raw
  · rintro rfl; exact split_join f

/-- Accepted fields consume their actual framed lengths, including on
noncanonical inputs. -/
theorem split_length {raw : List Bool} {f : Fields} (h : split raw = some f) :
    raw.length = 2 * (f.problem.length + f.epsilon.length + f.delta.length) + 3 + f.tape.length := by
  rw [split_some_raw h]
  simp only [join, List.length_append, Encoding.frame_length]
  omega

end Counting.Algorithm.KarpLubyRequest.Contract
