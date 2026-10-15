import ComplexCSP.Structure.MaltsevTypeStack

/-! # Exact continuation-stack execution and its transition count

The reference evaluator below uses the same finite list fold as materialized
search. Its cost counts literal successful control transitions, rather than
assuming a running-time oracle. The callbacks remain immutable arguments.
-/
namespace ComplexCSP.MaltsevTypeStack
open MaltsevWitness
variable {A : Type*} [DecidableEq A]

abbrev SearchResult (A : Type*) := (List A × ListTypeCache A) × ℕ

/-- The return frame schedules the first pending child, or finishes its parent. -/
def dispatch (len : ℕ) (target : List ℕ) (pending : List ℕ) (acc : List A)
    (stack : List (Frame A)) (cache : ListTypeCache A) : State A :=
  match pending with
  | [] => returnState len target acc stack ((len, acc) :: cache)
  | a :: rest => callState (len + 1) (replaceAt target len a)
      (⟨len, target, rest, acc⟩ :: stack) cache

/-- Child transitions include the one return transition that schedules the next
child, or pops the completed parent frame. -/
def childFold (children : List ℕ) (F : ℕ → ListTypeCache A → SearchResult A)
    (state : SearchResult A) : SearchResult A :=
  children.foldl (fun s a =>
    let next := F a s.1.2
    (((s.1.1 ++ next.1.1).dedup, next.1.2), s.2 + next.2 + 1)) state

/-- Structural reference evaluation, with an exact successful-transition count.
Fuel is only a proof/reference recursion parameter; it is absent from `State`. -/
def search (dimension : ℕ) (colors : List ℕ)
    (reconstruct : ℕ → List ℕ → Option (List ℕ)) (label : List ℕ → A) :
    ℕ → ℕ → List ℕ → ListTypeCache A → SearchResult A
  | fuel, len, target, cache =>
    match reconstruct len target with
    | none => (([], cache), 1)
    | some witness =>
      match cachedTypeList cache len (label witness) with
      | some labels => ((labels.dedup, cache), 1)
      | none =>
        match fuel with
        | 0 => (([label witness], (len, [label witness]) :: cache), 1)
        | fuel + 1 =>
          if len < dimension then
            let result := childFold colors
              (fun a c => search dimension colors reconstruct label fuel (len + 1)
                (replaceAt target len a) c) (([], cache), 0)
            ((result.1.1, (len, result.1.1) :: result.1.2), result.2 + 1)
          else (([label witness], (len, [label witness]) :: cache), 1)

@[simp] theorem step_return_frame (dimension : ℕ) (colors : List ℕ)
    (reconstruct : ℕ → List ℕ → Option (List ℕ)) (label : List ℕ → A)
    (childLen len : ℕ) (childTarget target : List ℕ) (returned acc : List A)
    (pending : List ℕ) (stack : List (Frame A)) (cache : ListTypeCache A) :
    step dimension colors reconstruct label
      (returnState childLen childTarget returned (⟨len,target,pending,acc⟩ :: stack) cache) =
    some (dispatch len target pending (acc ++ returned).dedup stack cache) := by
  cases pending <;> rfl

omit [DecidableEq A] in
@[simp] theorem step_halt (dimension : ℕ) (colors : List ℕ)
    (reconstruct : ℕ → List ℕ → Option (List ℕ)) (label : List ℕ → A)
    [DecidableEq A] (len : ℕ) (target : List ℕ) (labels : List A) (cache : ListTypeCache A) :
    step dimension colors reconstruct label (returnState len target labels [] cache) = none := rfl

/-- Execute the pending siblings of one explicit continuation frame. -/
theorem dispatch_runs (dimension : ℕ) (colors : List ℕ)
    (reconstruct : ℕ → List ℕ → Option (List ℕ)) (label : List ℕ → A)
    (len : ℕ) (target : List ℕ) (F : ℕ → ListTypeCache A → SearchResult A)
    (hF : ∀ a c stack, Runs (step dimension colors reconstruct label)
      (callState (len + 1) (replaceAt target len a) stack c)
      (returnState (len + 1) (replaceAt target len a) (F a c).1.1 stack (F a c).1.2)
      (F a c).2)
    (pending : List ℕ) (acc : List A) (stack : List (Frame A)) (cache : ListTypeCache A)
    (cost : ℕ) :
    Runs (step dimension colors reconstruct label)
      (dispatch len target pending acc stack cache)
      (let result := childFold pending F ((acc, cache), cost)
       returnState len target result.1.1 stack ((len, result.1.1) :: result.1.2))
      ((childFold pending F ((acc, cache), cost)).2 - cost) := by
  induction pending generalizing acc cache cost with
  | nil => simp only [dispatch, childFold, List.foldl_nil, Nat.sub_self]; exact Runs.refl _
  | cons a pending ih =>
    let next := F a cache
    let combined := (acc ++ next.1.1).dedup
    have hc := hF a cache (⟨len,target,pending,acc⟩ :: stack)
    have ht := Runs.step (step_return_frame dimension colors reconstruct label
      (len + 1) len (replaceAt target len a) target next.1.1 acc pending stack next.1.2)
      (ih combined next.1.2 (cost + next.2 + 1))
    have hrun := hc.trans ht
    have hmono : cost + next.2 + 1 ≤
        (childFold pending F ((combined, next.1.2), cost + next.2 + 1)).2 := by
      clear hc ht hrun ih
      generalize cost + next.2 + 1 = t
      generalize next.1.2 = c
      generalize combined = xs
      induction pending generalizing t c xs with
      | nil => simp [childFold]
      | cons b bs ih =>
        simp only [childFold, List.foldl_cons] at *
        exact (Nat.le_add_right t ((F b c).2 + 1)).trans (by simpa [Nat.add_assoc] using ih (t + (F b c).2 + 1) (F b c).1.2 (xs ++ (F b c).1.1).dedup)
    simpa only [dispatch, childFold, List.foldl_cons] using
      (show Runs (step dimension colors reconstruct label)
        (callState (len + 1) (replaceAt target len a)
          (⟨len,target,pending,acc⟩ :: stack) cache)
        (let r := childFold pending F ((combined, next.1.2), cost + next.2 + 1)
         returnState len target r.1.1 stack ((len,r.1.1) :: r.1.2))
        ((childFold pending F ((combined,next.1.2),cost + next.2 + 1)).2 - cost) from by
          dsimp only [next, combined] at hmono hrun ⊢
          convert hrun using 1
          omega)

/-- Exact simulation for every input whose remaining reference depth reaches the
dimension. No relation-correctness assumption is used in this control theorem. -/
theorem search_runs (dimension : ℕ) (colors : List ℕ)
    (reconstruct : ℕ → List ℕ → Option (List ℕ)) (label : List ℕ → A)
    (fuel len : ℕ) (hdepth : len + fuel = dimension) (target : List ℕ)
    (cache : ListTypeCache A) (stack : List (Frame A)) :
    Runs (step dimension colors reconstruct label) (callState len target stack cache)
      (returnState len target (search dimension colors reconstruct label fuel len target cache).1.1
        stack (search dimension colors reconstruct label fuel len target cache).1.2)
      (search dimension colors reconstruct label fuel len target cache).2 := by
  induction fuel generalizing len target cache stack with
  | zero =>
    have hlen : ¬len < dimension := by omega
    rw [search]
    cases hw : reconstruct len target with
    | none => exact Runs.step (by simp [step, callState, hw]) (Runs.refl _)
    | some w =>
      simp only []
      cases hc : cachedTypeList cache len (label w) with
      | none => exact Runs.step (by simp [step, callState, hw, hc, hlen]) (Runs.refl _)
      | some S => exact Runs.step (by simp [step, callState, hw, hc]) (Runs.refl _)
  | succ fuel ih =>
    have hlen : len < dimension := by omega
    rw [search]
    cases hw : reconstruct len target with
    | none => exact Runs.step (by simp [step, callState, hw]) (Runs.refl _)
    | some w =>
      simp only []
      cases hc : cachedTypeList cache len (label w) with
      | some S => exact Runs.step (by simp [step, callState, hw, hc]) (Runs.refl _)
      | none =>
        simp only [if_pos hlen]
        let F := fun a c => search dimension colors reconstruct label fuel (len + 1) (replaceAt target len a) c
        have hr := dispatch_runs dimension colors reconstruct label len target F
          (fun a c s => ih (len+1) (by omega) _ c s) colors [] stack cache 0
        simp only [Nat.sub_zero] at hr
        apply Runs.step _ hr
        cases colors <;> simp [step, callState, hw, hc, hlen, dispatch]

/-- Exact amortized child-transition bound: every completed branch installs a
cache entry, so the cost is charged to the concrete cache growth. -/
theorem childFold_cost_bound (children : List ℕ)
    (F : ℕ → ListTypeCache A → SearchResult A) (d : ℕ)
    (hF : ∀ a c, (F a c).2 + 1 + 2 * d * c.length ≤
      2 + 2 * d * (F a c).1.2.length) (state : SearchResult A) :
    (childFold children F state).2 + 2 * d * state.1.2.length ≤
      state.2 + 2 * children.length + 2 * d * (childFold children F state).1.2.length := by
  induction children generalizing state with
  | nil => simp [childFold]
  | cons a children ih =>
    have ht := ih (((state.1.1 ++ (F a state.1.2).1.1).dedup, (F a state.1.2).1.2),
      state.2 + (F a state.1.2).2 + 1)
    have hh := hF a state.1.2
    simp only [childFold, List.foldl_cons, List.length_cons] at ht ⊢
    omega

/-- Twice the call-count potential, minus the final halt: this bounds literal
control transitions for any callbacks and any cache, without a size oracle. -/
theorem search_cost_cache_bound (dimension : ℕ) (colors : List ℕ)
    (reconstruct : ℕ → List ℕ → Option (List ℕ)) (label : List ℕ → A)
    (fuel len : ℕ) (target : List ℕ) (cache : ListTypeCache A) :
    (search dimension colors reconstruct label fuel len target cache).2 + 1 +
      2 * colors.length * cache.length ≤
    2 + 2 * colors.length * (search dimension colors reconstruct label fuel len target cache).1.2.length := by
  induction fuel generalizing len target cache with
  | zero =>
    rw [search]
    cases hw : reconstruct len target with
    | none => simp
    | some w =>
      simp only []
      cases hc : cachedTypeList cache len (label w) <;> simp [Nat.mul_add]
  | succ fuel ih =>
    rw [search]
    cases hw : reconstruct len target with
    | none => simp
    | some w =>
      simp only []
      cases hc : cachedTypeList cache len (label w) with
      | some S => simp
      | none =>
        by_cases hlt : len < dimension
        · simp only [if_pos hlt]
          have ht := childFold_cost_bound colors
            (fun a c => search dimension colors reconstruct label fuel (len + 1)
              (replaceAt target len a) c) colors.length
            (fun a c => ih _ _ _) (([],cache),0)
          simp only [List.length_cons] at ht ⊢
          nlinarith
        · simp [hlt, Nat.mul_add]

end ComplexCSP.MaltsevTypeStack
