import Paper2.Complexity.BellMachines.UniversalPairReduction.SmoothingCompiler.ThreeQueryBound

/-! A decreasing actual-run potential identifies all query occurrences without
assuming that a syntactic query label is visited only once. -/
namespace Paper2.Complexity.BellMachines.QueryPotential

variable {A : Type} (step : A → Option A) (cost remaining : A → ℕ)
    (potential : ∀ a b, step a = some b → cost a + remaining b ≤ remaining a)
include potential

/-- Successful runs cannot increase the query potential. -/
theorem run_mono (n : ℕ) (a b : A)
    (h : (fun c : Option A => c.bind step)^[n] (some a) = some b) :
    remaining b ≤ remaining a := by
  induction n generalizing a with
  | zero =>
    have he : a = b := Option.some.inj h
    subst b
    exact Nat.le_refl _
  | succ n ih =>
    rw [Function.iterate_succ_apply, Option.bind_some] at h
    cases hs : step a with
    | none =>
      have hn : ∀ k, (fun c : Option A => c.bind step)^[k] none = none := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl
      rw [hs, hn] at h
      contradiction
    | some c =>
      rw [hs] at h
      have hp := potential a c hs
      exact (ih c h).trans (by omega)

/-- Starting from a query spends one potential unit before any later state. -/
theorem run_strict (n : ℕ) (hn : 0 < n) (a b : A)
    (hc : cost a = 1)
    (h : (fun c : Option A => c.bind step)^[n] (some a) = some b) :
    remaining b < remaining a := by
  cases n with
  | zero => omega
  | succ n =>
    rw [Function.iterate_succ_apply, Option.bind_some] at h
    cases hs : step a with
    | none =>
      have hz : ∀ k, (fun c : Option A => c.bind step)^[k] none = none := by
        intro k
        induction k with
        | zero => rfl
        | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl
      rw [hs, hz] at h
      contradiction
    | some c =>
      rw [hs] at h
      have hp := potential a c hs
      have hm := run_mono step cost remaining potential n c b h
      omega

/-- Two query states with equal remaining potential must be the same occurrence
of the same deterministic run, regardless of intervening stack contents. -/
theorem unique_query_time (start a b : A) (i j : ℕ)
    (hi : (fun c : Option A => c.bind step)^[i] (some start) = some a)
    (hj : (fun c : Option A => c.bind step)^[j] (some start) = some b)
    (ha : cost a = 1) (hb : cost b = 1) (he : remaining a = remaining b) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have ht : j = (j - i) + i := by omega
    rw [ht, Function.iterate_add_apply, hi] at hj
    have hs := run_strict step cost remaining potential (j - i) (by omega) a b ha hj
    omega
  · exact h
  · have ht : i = (i - j) + j := by omega
    rw [ht, Function.iterate_add_apply, hj] at hi
    have hs := run_strict step cost remaining potential (i - j) (by omega) b a hb hi
    omega

end Paper2.Complexity.BellMachines.QueryPotential
