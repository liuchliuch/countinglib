import ComplexCSP.Structure.MaltsevTypeStackCorrespondence
import ComplexCSP.Complexity.WitnessReconstruction

/-! # Concrete stored-witness callback for the type-search stack -/
namespace ComplexCSP.MaltsevTypeStack
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding ComplexityWitnessPrimitives
variable {A : Type*} [DecidableEq A] {d n : ℕ}

/-- The callback reads the actual materialized witness table and seed. -/
def storedReconstruct (m : Operation (Fin d)) (W : StoredCode d n)
    (len : ℕ) (target : List ℕ) : Option (List ℕ) :=
  (reconstructRawTo d (fun a b c => m (a,b,c)) (rawTable W) target (maybeWord W.seed) len).head?

omit [DecidableEq A] in
theorem storedReconstruct_word (m : Operation (Fin d)) (W : StoredCode d n)
    (len : ℕ) (hlen : len ≤ n) (x : Tuple (Fin d) n) :
    storedReconstruct m W len (word x) = (reconstructTo m W.toCode x len).map word := by
  rw [storedReconstruct, reconstructRawTo_stored m W x len hlen]
  cases reconstructTo m W.toCode x len <;> simp [maybeWord]

/-- Exact stack execution with the literal FP stored-table reconstruction,
leaving only the independently compiled row-label representation equation. -/
theorem stored_materialized_runs (m : Operation (Fin d)) (W : StoredCode d n)
    (label : Tuple (Fin d) n → A) (labelRaw : List ℕ → A)
    (hlab : ∀ x, labelRaw (word x) = label x)
    (fuel len : ℕ) (hdepth : len + fuel = n) (target : Tuple (Fin d) n)
    (cache : ListTypeCache A) (stack : List (Frame A)) :
    Runs (step n (List.range d) (storedReconstruct m W) labelRaw)
      (callState len (word target) stack cache)
      (returnState len (word target) (materializedTypeSearch m W.toCode label fuel len target cache).1
        stack (materializedTypeSearch m W.toCode label fuel len target cache).2)
      (search n (List.range d) (storedReconstruct m W) labelRaw fuel len (word target) cache).2 :=
  materialized_runs m W.toCode label (storedReconstruct m W) labelRaw
    (storedReconstruct_word m W) hlab fuel len hdepth target cache stack

/-- A bounded actual interpreter, used for execution tests and compiler bridges.
The successful terminal state is distinguished from exhaustion of the budget. -/
def run (transition : State A → Option (State A)) : ℕ → State A → Option (State A)
  | 0, _ => none
  | fuel + 1, s => match transition s with
    | none => some s
    | some t => run transition fuel t

omit [DecidableEq A] in
theorem Runs.run_eq {transition : State A → Option (State A)} {s t : State A} {steps : ℕ}
    (h : Runs transition s t steps) (ht : transition t = none) :
    run transition (steps + 1) s = some t := by
  induction h with
  | refl => simp [run, ht]
  | step he _ ih => simpa [run, he] using ih ht

omit [DecidableEq A] in
theorem run_mono {transition : State A → Option (State A)} {s t : State A} {budget : ℕ}
    (h : run transition budget s = some t) (extra : ℕ) :
    run transition (budget + extra) s = some t := by
  induction budget generalizing s with
  | zero => simp [run] at h
  | succ k ih =>
    cases hs : transition s with
    | none => simp [run,hs] at h; subst t; simp [run,hs,Nat.add_comm]
    | some u =>
      have hh : run transition k u = some t := by simpa [run,hs] using h
      simpa [run,hs,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using ih hh

/-- A fixed polynomial budget suffices for the real stack interpreter. Its
result is the exact materialized list/cache, rather than only its finite set. -/
theorem stored_run_polynomial {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : StoredCode d n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W.toCode R)
    (label : Tuple (Fin d) n → A) (hTP : TypesPartition R label)
    (labelRaw : List ℕ → A) (hlab : ∀ x, labelRaw (word x) = label x)
    (fuel len : ℕ) (hdepth : len + fuel = n) (target : Tuple (Fin d) n)
    (U : Finset A) (hU : ∀ x ∈ R, label (Vector.ofFn x) ∈ U) :
    run (step n (List.range d) (storedReconstruct m W) labelRaw)
      (2 * (1 + d * ((n + 1) * U.card))) (callState len (word target) [] []) =
    some (returnState len (word target) (materializedTypeSearch m W.toCode label fuel len target []).1
      [] (materializedTypeSearch m W.toCode label fuel len target []).2) := by
  have hr := (stored_materialized_runs m W label labelRaw hlab fuel len hdepth target [] []).run_eq
    (step_halt n (List.range d) (storedReconstruct m W) labelRaw _ _ _ _)
  have hb := materialized_transition_bound hm hR hW label hTP (storedReconstruct m W) labelRaw
    (storedReconstruct_word m W) hlab fuel len hdepth target U hU
  obtain ⟨extra,he⟩ := Nat.exists_eq_add_of_le hb
  rw [he]
  exact run_mono hr extra

end ComplexCSP.MaltsevTypeStack
