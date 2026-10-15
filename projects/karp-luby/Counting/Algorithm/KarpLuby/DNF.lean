import Mathlib.Data.Fin.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-!
# Explicit DNF syntax and normalization

The ambient number of variables is explicit. Repeated literals and repeated terms
are allowed; contradictory terms normalize to `none`. A normalized clause records
one optional constraint per variable, including variables absent from the input.
-/

namespace Counting.Algorithm.KarpLuby.DNF

abbrev Assignment (n : ℕ) := Fin n → Bool
abbrev RawTerm (n : ℕ) := List (Fin n × Bool)
abbrev Formula (n : ℕ) := List (RawTerm n)
abbrev Clause (n : ℕ) := Fin n → Option Bool

variable {n : ℕ}

def evalTerm (t : RawTerm n) (a : Assignment n) : Bool :=
  t.all fun l => a l.1 == l.2

def evalDNF (f : Formula n) (a : Assignment n) : Bool :=
  f.any fun t => evalTerm t a

def Satisfies (c : Clause n) (a : Assignment n) : Prop :=
  ∀ i b, c i = some b → a i = b

instance (c : Clause n) (a : Assignment n) : Decidable (Satisfies c a) :=
  inferInstanceAs (Decidable (∀ i b, c i = some b → a i = b))

def evalClause : {n : ℕ} → Clause n → Assignment n → Bool
  | 0, _, _ => true
  | _ + 1, c, a =>
    match c 0 with
    | none => evalClause (fun i => c i.succ) (fun i => a i.succ)
    | some b => (a 0 == b) && evalClause (fun i => c i.succ) (fun i => a i.succ)

theorem satisfies_succ (c : Clause (n + 1)) (a : Assignment (n + 1)) :
    Satisfies c a ↔ (∀ b, c 0 = some b → a 0 = b) ∧
      Satisfies (fun i => c i.succ) (fun i => a i.succ) := by
  constructor
  · intro h
    exact ⟨h 0, fun i => h i.succ⟩
  · rintro ⟨h0, ht⟩ i
    refine Fin.cases h0 (fun j => ht j) i

@[simp] theorem evalClause_eq_true (c : Clause n) (a : Assignment n) :
    evalClause c a = true ↔ Satisfies c a := by
  induction n with
  | zero => simp [evalClause, Satisfies]
  | succ n ih =>
    rw [satisfies_succ]
    cases hc : c 0 <;> simp [evalClause, hc, ih]

@[simp] theorem evalTerm_nil (a : Assignment n) : evalTerm [] a = true := rfl

@[simp] theorem evalTerm_cons (l : Fin n × Bool) (t : RawTerm n) (a : Assignment n) :
    evalTerm (l :: t) a = true ↔ a l.1 = l.2 ∧ evalTerm t a = true := by
  simp [evalTerm]

@[simp] theorem evalDNF_eq_true (f : Formula n) (a : Assignment n) :
    evalDNF f a = true ↔ ∃ t ∈ f, evalTerm t a = true := by simp [evalDNF]

/-- Add a literal, rejecting precisely an incompatible existing constraint. -/
def insertLiteral (c : Clause n) (l : Fin n × Bool) : Option (Clause n) :=
  match c l.1 with
  | none => some (Function.update c l.1 (some l.2))
  | some b => if b = l.2 then some c else none

/-- Normalization visits literals once; each update preserves all other variables. -/
def normalize : RawTerm n → Option (Clause n)
  | [] => some (fun _ => none)
  | l :: t => (normalize t).bind fun c => insertLiteral c l

/-- The semantics of rejection is the empty set of assignments. -/
def NormalizedSatisfies (o : Option (Clause n)) (a : Assignment n) : Prop :=
  ∃ c, o = some c ∧ Satisfies c a

@[simp] theorem normalizedSatisfies_none (a : Assignment n) :
    ¬ NormalizedSatisfies none a := by simp [NormalizedSatisfies]

@[simp] theorem normalizedSatisfies_some (c : Clause n) (a : Assignment n) :
    NormalizedSatisfies (some c) a ↔ Satisfies c a := by simp [NormalizedSatisfies]

theorem satisfies_update (c : Clause n) (a : Assignment n) (i : Fin n) (b : Bool)
    (hi : c i = none) :
    Satisfies (Function.update c i (some b)) a ↔ a i = b ∧ Satisfies c a := by
  constructor
  · intro h
    refine ⟨h i b (by simp), ?_⟩
    intro j d hj
    have hji : j ≠ i := by intro he; subst j; simp [hi] at hj
    exact h j d (by simpa [Function.update, hji, Ne.symm hji] using hj)
  · rintro ⟨hab, h⟩ j d hj
    by_cases hji : j = i
    · subst j
      simpa using hab.trans (by simpa using hj)
    · apply h j d
      simpa [Function.update, hji, Ne.symm hji] using hj

theorem insertLiteral_correct (c : Clause n) (l : Fin n × Bool) (a : Assignment n) :
    NormalizedSatisfies (insertLiteral c l) a ↔ Satisfies c a ∧ a l.1 = l.2 := by
  unfold insertLiteral
  cases hc : c l.1 with
  | none => simp [satisfies_update c a l.1 l.2 hc, and_comm]
  | some b =>
    by_cases hb : b = l.2
    · subst b
      simp only [ite_true, normalizedSatisfies_some]
      exact ⟨fun h => ⟨h, h l.1 l.2 hc⟩, And.left⟩
    · simp only [hb, ↓reduceIte, normalizedSatisfies_none, false_iff, not_and]
      intro h he
      exact hb ((h l.1 b hc).symm.trans he)

theorem normalize_correct (t : RawTerm n) (a : Assignment n) :
    NormalizedSatisfies (normalize t) a ↔ evalTerm t a = true := by
  induction t with
  | nil => simp [normalize, Satisfies]
  | cons l t ih =>
    simp only [normalize]
    cases ht : normalize t with
    | none =>
      simp only [ht, normalizedSatisfies_none] at ih
      simpa only [Option.bind_none, normalizedSatisfies_none, evalTerm_cons] using
        (show False ↔ a l.1 = l.2 ∧ evalTerm t a = true from
          ⟨False.elim, fun h => ih.mpr h.2⟩)
    | some c =>
      simp only [ht, normalizedSatisfies_some] at ih
      simpa only [Option.bind_some, insertLiteral_correct, evalTerm_cons, and_comm] using
        (and_congr ih (Iff.rfl : a l.1 = l.2 ↔ a l.1 = l.2))

/-- Removing contradictory terms leaves DNF semantics unchanged; duplicate terms remain. -/
def normalizeFormula (f : Formula n) : List (Clause n) := f.filterMap normalize

theorem normalizeFormula_correct (f : Formula n) (a : Assignment n) :
    (∃ c ∈ normalizeFormula f, Satisfies c a) ↔ evalDNF f a = true := by
  simp only [normalizeFormula, List.mem_filterMap, evalDNF_eq_true]
  constructor
  · rintro ⟨c, ⟨t, ht, hc⟩, ha⟩
    exact ⟨t, ht, (normalize_correct t a).mp ⟨c, hc, ha⟩⟩
  · rintro ⟨t, ht, ha⟩
    obtain ⟨c, hc, hca⟩ := (normalize_correct t a).mpr ha
    exact ⟨c, ⟨t, ht, hc⟩, hca⟩

end Counting.Algorithm.KarpLuby.DNF
