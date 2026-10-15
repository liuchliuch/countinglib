import Counting.Algorithm.KarpLubyRequest.Dense.NormalizeRun

/-!
# Original raw-term codec to the concrete finite normalizer

All accepted representations are covered. The theorem consumes a disposable raw
term while retaining the original variable word, and returns the exact existing
`DenseNormalization.normalize` value with clean work stacks. Its cost depends on
physical input lengths, including noncanonical list and natural headers.
-/
namespace Counting.Algorithm.KarpLubyRequest.Dense.Normalize
open Turing Computability Holant.Complexity StackProtocol
open Counting.Algorithm.KarpLuby Counting.Algorithm.KarpLubyMachine

private theorem mapM_parts {n : ℕ} (raws : List (List Bool)) (term : DNF.RawTerm n)
    (h : raws.mapM (Encoding.literal n).decode = some term) :
    ∃ words : List RawLiteral,
      words.map literalWord = raws ∧ words.map literalValue = term.map (fun l => (l.1.val, l.2)) := by
  induction raws generalizing term with
  | nil =>
    have ht : term = [] := by simpa using h.symm
    subst term
    exact ⟨[], rfl, rfl⟩
  | cons raw raws ih =>
    cases hd : (Encoding.literal n).decode raw with
    | none => simp [List.mapM_cons, hd] at h
    | some l =>
      cases ht : raws.mapM (Encoding.literal n).decode with
      | none => simp [List.mapM_cons, hd, ht] at h
      | some ts =>
        have he : l :: ts = term := by simpa [List.mapM_cons, hd, ht] using h
        subst term
        obtain ⟨index, hr, hv⟩ := literal_parts raw l hd
        obtain ⟨words, hw, hs⟩ := ih ts ht
        refine ⟨(index, l.2) :: words, ?_, ?_⟩
        · simp only [List.map_cons, hw, ← hr]
        · simp only [List.map_cons, literalValue, hv, hs]

/-- Exact raw decomposition recovered from the original successful decoder. -/
theorem raw_parts {n : ℕ} (raw : List Bool) (term : DNF.RawTerm n)
    (h : (Encoding.list (Encoding.literal n)).decode raw = some term) :
    ∃ header : List Bool, ∃ words : List RawLiteral,
      decodeNat header = words.length ∧
      raw = Encoding.frame header ++ Encoding.frames (words.map literalWord) ∧
      words.map literalValue = term.map (fun l => (l.1.val, l.2)) := by
  rw [ListFields.list_decode_eq] at h
  cases hs : ListFields.split raw with
  | none => simp [hs] at h
  | some raws =>
    simp only [hs, Option.bind_some] at h
    obtain ⟨header, hcount, hraw⟩ := (ListFields.split_some_iff raw raws).mp hs
    obtain ⟨words, hw, hv⟩ := mapM_parts raws term h
    refine ⟨header, words, ?_, ?_, hv⟩
    · rw [← hw, List.length_map] at hcount
      exact hcount
    · rw [← hw] at hraw
      exact hraw

theorem literalWords_length (words : List RawLiteral) :
    ((words.map literalWord).map List.length).sum = 2 * indexBits words + 2 * words.length := by
  induction words with
  | nil => rfl
  | cons l words ih =>
    simp only [List.map_cons, List.sum_cons, literalWord, List.length_append, Encoding.frame_length,
      List.length_singleton, ih, indexBits_cons, List.length_cons, List.length_nil]
    ring

@[simp] theorem indexBits_reverse (words : List RawLiteral) : indexBits words.reverse = indexBits words := by
  simp only [indexBits, List.map_reverse, List.sum_reverse]

@[simp] theorem loopCost_reverse (n : ℕ) (words : List RawLiteral) :
    loopCost n words.reverse = loopCost n words := by
  simp only [loopCost, indexBits_reverse, List.length_reverse]

/-- A polynomial in actual variable-header and raw-term lengths, before any
conversion to a single request-size parameter. -/
def rawCost (n size : ℕ) : ℕ := 10 * n * size + 43 * size + 3 * n + 8

variable {τ : Type} (old : Bool) (memory : τ)

theorem normalize_raw (original raw : List Bool) (term : DNF.RawTerm original.length)
    (h : (Encoding.list (Encoding.literal original.length)).decode raw = some term) :
    ∃ bit : Bool, ∃ time : ℕ, time ≤ rawCost original.length raw.length ∧
      RunsExactly (TM2.step (program (τ := τ)))
        (cfg .headerScan (old, memory) (tapes original raw [] [] [] [] [] []))
        (finished bit memory original (DenseNormalization.normalize original.length term).value) time := by
  obtain ⟨header, words, _, hraw, hwords⟩ := raw_parts raw term h
  obtain ⟨bit, time, bound, run⟩ := normalize_prepared old memory original header words term hwords
  rw [← hraw] at run
  refine ⟨bit, time, ?_, run⟩
  have size : raw.length = 2 * header.length + 1 + 4 * indexBits words + 5 * words.length := by
    rw [hraw, List.length_append, Encoding.frame_length, framedWords_length]
    omega
  have hh : header.length ≤ raw.length := by omega
  have hi : indexBits words ≤ raw.length := by omega
  have hw : words.length ≤ raw.length := by omega
  have hs : 2 * indexBits words + 2 * words.length ≤ raw.length := by omega
  have hp := Nat.mul_le_mul_left (original.length + 1)
    (show 2 * indexBits words + 8 * words.length ≤ 10 * raw.length by omega)
  rw [literalWords_length, loopCost_reverse, loopCost] at bound
  unfold rawCost
  nlinarith

/-- Primitive cost is charged on the same real execution of the concrete
program. The finite control has budget at most eight per transition. -/
theorem normalize_raw_primitive (original raw : List Bool) (term : DNF.RawTerm original.length)
    (h : (Encoding.list (Encoding.literal original.length)).decode raw = some term) :
    ∃ bit : Bool, ∃ time : ℕ, time ≤ rawCost original.length raw.length ∧
      (GraphPreprocessing.Primitive.run (program (τ := τ)) time
        (some (cfg .headerScan (old, memory) (tapes original raw [] [] [] [] [] [])))).2 =
        some (finished bit memory original (DenseNormalization.normalize original.length term).value) ∧
      (GraphPreprocessing.Primitive.run (program (τ := τ)) time
        (some (cfg .headerScan (old, memory) (tapes original raw [] [] [] [] [] [])))).1 ≤ 8 * time := by
  obtain ⟨bit, time, bound, run⟩ := normalize_raw old memory original raw term h
  exact ⟨bit, time, bound, GraphPreprocessing.Primitive.execution_cost program 8 statement_budget _ _ _ run⟩

end Counting.Algorithm.KarpLubyRequest.Dense.Normalize
