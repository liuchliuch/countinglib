import Counting.Algorithm.KarpLubyRequest.ListFields
import Counting.Algorithm.KarpLubyRequest.LiteralFields

/-!
# Exact raw semantics for two nested list verifiers

The Boolean specifications here are the split/all operations used by the actual
list compiler. They agree with the original decoders on every raw word, not just
on canonical encodings. Raw element words, order and multiplicities are retained;
length bounds use their physical input size, never the decoded binary header.
No machine or complexity theorem is assumed by this semantic bridge.
-/
namespace Counting.Algorithm.KarpLubyRequest.NestedSemantics

open Counting.Algorithm.KarpLuby

/-- The raw list boundary followed by validation of every physical element. -/
def listAccepts (p : List Bool → Bool) (raw : List Bool) : Bool :=
  match ListFields.split raw with
  | none => false
  | some words => words.all p

def literalAccepts (n : ℕ) (raw : List Bool) : Bool :=
  (LiteralFields.separate n raw).isSome

def clauseAccepts (n : ℕ) : List Bool → Bool := listAccepts (literalAccepts n)

def formulaAccepts (n : ℕ) : List Bool → Bool := listAccepts (clauseAccepts n)

/-- Successful traversal means every decoder succeeds, including for an empty list. -/
theorem allDecoded_isSome {α β : Type} (f : α → Option β) (xs : List α) :
    (xs.mapM f).isSome = xs.all (fun x => (f x).isSome) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hf : f x <;> cases hs : xs.mapM f <;>
      simp_all [List.mapM_cons]

/-- Sequential element decoding can be factored through the retained raw fields. -/
theorem mapM_bind {α β γ : Type} (f : α → Option β) (g : β → Option γ)
    (xs : List α) :
    xs.mapM (fun x => (f x).bind g) = (xs.mapM f).bind (fun ys => ys.mapM g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases hf : f x with
    | none => simp [List.mapM_cons, hf]
    | some y =>
      cases hs : xs.mapM f <;> cases hg : g y <;>
        simp [List.mapM_cons, hf, ih, hs, hg]

/-- No occurrence is lost or duplicated by a successful Option traversal. -/
theorem mapM_length {α β : Type} (f : α → Option β) {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil =>
    simp at h
    subst ys
    rfl
  | cons x xs ih =>
    cases hf : f x with
    | none => simp [List.mapM_cons, hf] at h
    | some y =>
      cases hs : xs.mapM f with
      | none => simp [List.mapM_cons, hf, hs] at h
      | some more =>
        simp [List.mapM_cons, hf, hs] at h
        subst ys
        simpa only [List.length_cons] using congrArg Nat.succ (ih hs)

/-- Summed output weights are bounded by the physical weights of the input list. -/
theorem mapM_weight_le {α β : Type} (f : α → Option β)
    (inputWeight : α → ℕ) (outputWeight : β → ℕ)
    (bound : ∀ a b, f a = some b → outputWeight b ≤ inputWeight a)
    {xs : List α} {ys : List β} (h : xs.mapM f = some ys) :
    (ys.map outputWeight).sum ≤ (xs.map inputWeight).sum := by
  induction xs generalizing ys with
  | nil =>
    simp at h
    subst ys
    exact Nat.le_refl _
  | cons x xs ih =>
    cases hf : f x with
    | none => simp [List.mapM_cons, hf] at h
    | some y =>
      cases hs : xs.mapM f with
      | none => simp [List.mapM_cons, hf, hs] at h
      | some more =>
        simp [List.mapM_cons, hf, hs] at h
        subst ys
        simpa only [List.map_cons, List.sum_cons] using
          Nat.add_le_add (bound x y hf) (ih hs)

/-- The generic split/all specification is exactly the original list decoder's status. -/
theorem list_isSome_eq {α : Type} (e : Encoding.BitEncoding α) (raw : List Bool) :
    listAccepts (fun word => (e.decode word).isSome) raw =
      ((Encoding.list e).decode raw).isSome := by
  rw [ListFields.list_decode_eq]
  cases hs : ListFields.split raw <;>
    simp [listAccepts, hs, allDecoded_isSome]

/-- Range and polarity failures are precisely the original literal failures. -/
theorem literal_isSome_eq (n : ℕ) (raw : List Bool) :
    literalAccepts n raw = ((Encoding.literal n).decode raw).isSome := by
  have h := congrArg Option.isSome (LiteralFields.literal_decode_eq n raw)
  simpa only [Option.isSome_map, literalAccepts] using h.symm

theorem clause_isSome_eq (n : ℕ) (raw : List Bool) :
    clauseAccepts n raw = ((Encoding.list (Encoding.literal n)).decode raw).isSome := by
  change listAccepts (fun word => literalAccepts n word) raw = _
  simp_rw [literal_isSome_eq]
  exact list_isSome_eq (Encoding.literal n) raw

/-- Both actual raw-list validation levels match the unchanged formula codec. -/
theorem formula_isSome_eq (n : ℕ) (raw : List Bool) :
    formulaAccepts n raw = ((Encoding.formula n).decode raw).isSome := by
  change listAccepts (fun word => clauseAccepts n word) raw = _
  simp_rw [clause_isSome_eq]
  exact list_isSome_eq (Encoding.list (Encoding.literal n)) raw

theorem formula_rejects_iff (n : ℕ) (raw : List Bool) :
    formulaAccepts n raw = false ↔ (Encoding.formula n).decode raw = none := by
  rw [formula_isSome_eq]
  cases (Encoding.formula n).decode raw <;> simp

theorem formula_accepts_iff (n : ℕ) (raw : List Bool) :
    formulaAccepts n raw = true ↔ ∃ f, (Encoding.formula n).decode raw = some f := by
  rw [formula_isSome_eq]
  cases (Encoding.formula n).decode raw <;> simp

@[simp] theorem formulaAccepts_encode (n : ℕ) (f : DNF.Formula n) :
    formulaAccepts n ((Encoding.formula n).encode f) = true := by
  rw [formula_isSome_eq, (Encoding.formula n).decode_encode]
  rfl

/-- Two raw framing levels, retaining every literal word before its validation. -/
def splitNested (raw : List Bool) : Option (List (List (List Bool))) :=
  (ListFields.split raw).bind (fun clauses => clauses.mapM ListFields.split)

/-- Exact decoded values, rather than merely equivalent acceptance predicates. -/
theorem formula_decode_eq (n : ℕ) (raw : List Bool) :
    (Encoding.formula n).decode raw =
      (splitNested raw).bind (fun clauses =>
        clauses.mapM (fun words => words.mapM (Encoding.literal n).decode)) := by
  change (Encoding.list (Encoding.list (Encoding.literal n))).decode raw = _
  rw [ListFields.list_decode_eq]
  change (ListFields.split raw).bind (fun clauses =>
    clauses.mapM (fun word => (Encoding.list (Encoding.literal n)).decode word)) = _
  simp_rw [ListFields.list_decode_eq]
  simp only [mapM_bind, splitNested, Option.bind_assoc]

/-- Both list headers may use any raw word accepted by the original natural decoder. -/
@[simp] theorem splitNested_encode (n : ℕ) (f : DNF.Formula n) :
    splitNested ((Encoding.formula n).encode f) =
      some (f.map (fun clause => clause.map (Encoding.literal n).encode)) := by
  change (ListFields.split ((Encoding.list (Encoding.list (Encoding.literal n))).encode f)).bind
    (fun clauses => clauses.mapM ListFields.split) = _
  rw [ListFields.split_encode]
  change (f.map (Encoding.list (Encoding.literal n)).encode).mapM ListFields.split = _
  induction f with
  | nil => rfl
  | cons clause clauses ih =>
    simp [List.mapM_cons, ListFields.split_encode, ih]

/-- Clause count, literal count and literal payload bits are all physically paid for. -/
theorem splitNested_size {raw : List Bool} {clauses : List (List (List Bool))}
    (h : splitNested raw = some clauses) :
    clauses.length ≤ raw.length ∧
      (clauses.map List.length).sum ≤ raw.length ∧
      (clauses.map (fun words => (words.map List.length).sum)).sum ≤ raw.length := by
  cases hs : ListFields.split raw with
  | none => simp [splitNested, hs] at h
  | some words =>
    have hm : words.mapM ListFields.split = some clauses := by
      simpa only [splitNested, hs, Option.bind_some] using h
    obtain ⟨hc, hw⟩ := ListFields.split_size hs
    have hl := mapM_length ListFields.split hm
    have hn := mapM_weight_le ListFields.split List.length List.length
      (fun _ _ h => (ListFields.split_size h).1) hm
    have hb := mapM_weight_le ListFields.split List.length
      (fun literals => (literals.map List.length).sum)
      (fun _ _ h => (ListFields.split_size h).2) hm
    exact ⟨by omega, hn.trans hw, hb.trans hw⟩

/-- The occurrence bound applies to every successfully decoded raw list. -/
theorem list_decode_size {α : Type} (e : Encoding.BitEncoding α)
    {raw : List Bool} {xs : List α} (h : (Encoding.list e).decode raw = some xs) :
    xs.length ≤ raw.length := by
  rw [ListFields.list_decode_eq] at h
  cases hs : ListFields.split raw with
  | none => simp [hs] at h
  | some words =>
    have hm : words.mapM e.decode = some xs := by simpa only [hs, Option.bind_some] using h
    have hl := mapM_length e.decode hm
    have hc := (ListFields.split_size hs).1
    omega

/-- Decoded formula sizes are bounded by the actual accepted word, including
noncanonical headers and repeated literal occurrences. -/
theorem formula_decode_size (n : ℕ) {raw : List Bool} {f : DNF.Formula n}
    (h : (Encoding.formula n).decode raw = some f) :
    f.length ≤ raw.length ∧ (f.map List.length).sum ≤ raw.length := by
  have hc := list_decode_size (Encoding.list (Encoding.literal n)) h
  change (Encoding.list (Encoding.list (Encoding.literal n))).decode raw = some f at h
  rw [ListFields.list_decode_eq] at h
  cases hs : ListFields.split raw with
  | none => simp [hs] at h
  | some words =>
    have hm : words.mapM (Encoding.list (Encoding.literal n)).decode = some f := by
      simpa only [hs, Option.bind_some] using h
    have hl := mapM_weight_le (Encoding.list (Encoding.literal n)).decode List.length List.length
      (fun _ _ h => list_decode_size (Encoding.literal n) h) hm
    exact ⟨hc, hl.trans (ListFields.split_size hs).2⟩

/-- R1's unary variable codec reads the length of every raw header, irrespective
of its bit values; the remaining formula is the original untouched suffix. -/
theorem input_decode_eq (raw : List Bool) :
    Encoding.input.decode raw = (Encoding.unframe raw).bind (fun p =>
      ((Encoding.formula p.1.length).decode p.2).bind (fun f =>
        some (⟨p.1.length, f⟩ : Encoding.Input))) := rfl

/-- Successful inputs expose the original raw fields and the exact dependent
formula, with no re-encoding or canonical-word restriction. -/
theorem input_decode_some_iff (raw : List Bool) (x : Encoding.Input) :
    Encoding.input.decode raw = some x ↔
      ∃ (header body : List Bool) (f : DNF.Formula header.length),
        Encoding.unframe raw = some (header, body) ∧
        (Encoding.formula header.length).decode body = some f ∧
        (⟨header.length, f⟩ : Encoding.Input) = x := by
  constructor
  · intro h
    cases hu : Encoding.unframe raw with
    | none => simp [input_decode_eq, hu] at h
    | some p =>
      rcases p with ⟨header, body⟩
      cases hf : (Encoding.formula header.length).decode body with
      | none => simp [input_decode_eq, hu, hf] at h
      | some f =>
        have hx : (⟨header.length, f⟩ : Encoding.Input) = x := by
          simpa only [input_decode_eq, hu, Option.bind_some, hf, Option.some.injEq] using h
        exact ⟨header, body, f, rfl, hf, hx⟩
  · rintro ⟨header, body, f, hu, hf, rfl⟩
    simp [input_decode_eq, hu, hf]

/-- H1's exact framing identity, transported to the uniquely owned R1 grammar. -/
theorem unframe_raw {raw header body : List Bool}
    (h : Encoding.unframe raw = some (header, body)) :
    raw = Encoding.frame header ++ body := by
  rw [Contract.unframe_eq] at h
  simpa only [Contract.frame_eq] using
    (Holant.Complexity.GraphPreprocessing.Frame.unframe_some_iff raw header body).mp h

/-- Exact physical size at the problem header boundary, valid also when its
formula body subsequently fails validation. -/
theorem unframe_size {raw header body : List Bool}
    (h : Encoding.unframe raw = some (header, body)) :
    raw.length = 2 * header.length + body.length + 1 ∧
      header.length ≤ raw.length ∧ body.length ≤ raw.length := by
  have hl := congrArg List.length (unframe_raw h)
  simp only [List.length_append, Encoding.frame_length] at hl
  omega

/-- A handoff preserving the exact raw variable word and physical formula body. -/
theorem input_decode_fields {raw : List Bool} {x : Encoding.Input}
    (h : Encoding.input.decode raw = some x) :
    ∃ (header body : List Bool) (f : DNF.Formula header.length),
      Encoding.unframe raw = some (header, body) ∧
      raw = Encoding.frame header ++ body ∧
      (Encoding.formula header.length).decode body = some f ∧
      x = (⟨header.length, f⟩ : Encoding.Input) ∧
      raw.length = 2 * header.length + body.length + 1 ∧
      header.length ≤ raw.length ∧ body.length ≤ raw.length := by
  obtain ⟨header, body, f, hu, hf, hx⟩ := (input_decode_some_iff raw x).mp h
  exact ⟨header, body, f, hu, unframe_raw hu, hf, hx.symm, unframe_size hu⟩

/-- Every successfully decoded raw problem pays for its ambient variables,
clause occurrences and literal occurrences, including unused and repeated ones. -/
theorem input_decode_size {raw : List Bool} {x : Encoding.Input}
    (h : Encoding.input.decode raw = some x) :
    x.variableCount ≤ raw.length ∧ x.formula.length ≤ raw.length ∧
      (x.formula.map List.length).sum ≤ raw.length := by
  obtain ⟨header, body, f, hu, hf, rfl⟩ := (input_decode_some_iff raw x).mp h
  obtain ⟨_, hh, hb⟩ := unframe_size hu
  obtain ⟨hc, hl⟩ := formula_decode_size header.length hf
  exact ⟨hh, hc.trans hb, hl.trans hb⟩

end Counting.Algorithm.KarpLubyRequest.NestedSemantics
