import ComplexCSP.Structure.MaltsevTypeCache

/-! # An executable call trace and polynomial type-search call bound -/
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {d n : ℕ} {A : Type*} [DecidableEq A]

abbrev TypeRun (A : Type*) := (Finset A × TypeCache A) × ℕ

def traceChildren (children : List (Fin d)) (F : Fin d → TypeCache A → TypeRun A)
    (state : TypeRun A) : TypeRun A :=
  children.foldl (fun state a =>
    let next := F a state.1.2
    ((state.1.1 ∪ next.1.1, next.1.2), state.2 + next.2)) state

def tracedTypeSearch (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) : ℕ → ℕ → Tuple (Fin d) n → TypeCache A → TypeRun A
  | fuel, len, target, cache =>
    match reconstructTo m W target len with
    | none => ((∅, cache), 1)
    | some w =>
      match cachedType cache len (label w) with
      | some S => ((S, cache), 1)
      | none =>
        match fuel with
        | 0 => (({label w}, (len, {label w}) :: cache), 1)
        | fuel + 1 =>
          if h : len < n then
            let result := traceChildren (List.finRange d)
              (fun a c => tracedTypeSearch m W label fuel (len + 1)
                (replaceCoordinate target ⟨len, h⟩ a) c) ((∅, cache), 1)
            ((result.1.1, (len, result.1.1) :: result.1.2), result.2)
          else (({label w}, (len, {label w}) :: cache), 1)

theorem traceChildren_first (children : List (Fin d))
    (F : Fin d → TypeCache A → TypeRun A)
    (G : Fin d → TypeCache A → Finset A × TypeCache A)
    (hFG : ∀ a c, (F a c).1 = G a c) (state : TypeRun A) :
    (traceChildren children F state).1 =
      children.foldl (fun state a => let next := G a state.2;
        (state.1 ∪ next.1, next.2)) state.1 := by
  induction children generalizing state with
  | nil => rfl
  | cons a children ih =>
    simp only [traceChildren, List.foldl_cons] at ih ⊢
    rw [ih]
    simp only [hFG]

theorem tracedTypeSearch_first (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (fuel len : ℕ) (target : Tuple (Fin d) n) (cache : TypeCache A) :
    (tracedTypeSearch m W label fuel len target cache).1 = typeSearch m W label fuel len target cache := by
  induction fuel generalizing len target cache with
  | zero =>
    rw [tracedTypeSearch, typeSearch]
    cases hw : reconstructTo m W target len with
    | none => rfl
    | some w =>
      simp only []
      cases hc : cachedType cache len (label w) <;> rfl
  | succ fuel ih =>
    rw [tracedTypeSearch, typeSearch]
    cases hw : reconstructTo m W target len with
    | none => rfl
    | some w =>
      simp only []
      cases hc : cachedType cache len (label w) with
      | some S => rfl
      | none =>
        by_cases hlt : len < n
        · simp only [dif_pos hlt]
          have ht := traceChildren_first (List.finRange d)
            (fun a c => tracedTypeSearch m W label fuel (len + 1) (replaceCoordinate target ⟨len, hlt⟩ a) c)
            (fun a c => typeSearch m W label fuel (len + 1) (replaceCoordinate target ⟨len, hlt⟩ a) c)
            (fun a c => ih _ _ _) ((∅, cache), 1)
          exact congrArg (fun p : Finset A × TypeCache A => (p.1, (len, p.1) :: p.2)) ht
        · simp only [dif_neg hlt]

theorem traceChildren_bound (children : List (Fin d))
    (F : Fin d → TypeCache A → TypeRun A)
    (hF : ∀ a c, (F a c).2 + d * c.length ≤ 1 + d * (F a c).1.2.length)
    (state : TypeRun A) :
    (traceChildren children F state).2 + d * state.1.2.length ≤
      state.2 + children.length + d * (traceChildren children F state).1.2.length := by
  induction children generalizing state with
  | nil => simp [traceChildren]
  | cons a children ih =>
    have ht := ih ((state.1.1 ∪ (F a state.1.2).1.1, (F a state.1.2).1.2), state.2 + (F a state.1.2).2)
    have hh := hF a state.1.2
    simp only [traceChildren, List.foldl_cons, List.length_cons] at ht ⊢
    omega

/-- Each branching call creates a new cache entry. The exact recursive call
count is bounded by the increase in cache length, with no hidden search oracle. -/
theorem tracedTypeSearch_calls_le (m : Operation (Fin d)) (W : Code (Fin d) n)
    (label : Tuple (Fin d) n → A) (fuel len : ℕ) (target : Tuple (Fin d) n) (cache : TypeCache A) :
    (tracedTypeSearch m W label fuel len target cache).2 + d * cache.length ≤
      1 + d * (tracedTypeSearch m W label fuel len target cache).1.2.length := by
  induction fuel generalizing len target cache with
  | zero =>
    rw [tracedTypeSearch]
    cases hw : reconstructTo m W target len with
    | none => rfl
    | some w =>
      simp only []
      cases hc : cachedType cache len (label w) with
      | some S => rfl
      | none => simp only [List.length_cons]; nlinarith
  | succ fuel ih =>
    rw [tracedTypeSearch]
    cases hw : reconstructTo m W target len with
    | none => rfl
    | some w =>
      simp only []
      cases hc : cachedType cache len (label w) with
      | some S => rfl
      | none =>
        by_cases hlt : len < n
        · simp only [dif_pos hlt]
          have ht := traceChildren_bound (List.finRange d)
            (fun a c => tracedTypeSearch m W label fuel (len + 1) (replaceCoordinate target ⟨len, hlt⟩ a) c)
            (fun a c => ih _ _ _) ((∅, cache), 1)
          simp only [List.length_finRange, List.length_cons] at ht ⊢
          nlinarith
        · simp only [dif_neg hlt, List.length_cons]
          nlinarith

/-- The literal type-search execution makes at most `1+d*(n+1)*|U|` calls.
This operation-count theorem is distinct from the later bit-machine compiler. -/
theorem typeSearch_call_bound {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (label : Tuple (Fin d) n → A) (hTP : TypesPartition R label)
    (fuel len : ℕ) (hdepth : len + fuel = n) (target : Tuple (Fin d) n)
    (U : Finset A) (hU : ∀ x ∈ R, label (Vector.ofFn x) ∈ U) :
    (tracedTypeSearch m W label fuel len target []).2 ≤ 1 + d * ((n + 1) * U.card) := by
  have hc := tracedTypeSearch_calls_le m W label fuel len target []
  rw [tracedTypeSearch_first] at hc
  have hl := typeSearch_cache_length_le hm hR hW label hTP fuel len hdepth target U hU
  simp only [List.length_nil, mul_zero, add_zero] at hc
  exact hc.trans (Nat.add_le_add_left (Nat.mul_le_mul_left d hl) 1)

end ComplexCSP.MaltsevWitness
