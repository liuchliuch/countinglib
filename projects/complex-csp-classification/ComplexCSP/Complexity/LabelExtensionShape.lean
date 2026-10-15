import ComplexCSP.Complexity.LabelExtensionCorrectness

set_option backward.isDefEq.respectTransparency false

/-! # Unconditional stored-context output shape

No correctness of the support table, Mal'tsev identity, query outcome or space
cap is assumed. Raw capped queries may fail arbitrarily; returned words still
have the exact typed length and finite color alphabet.
-/
namespace ComplexCSP.ComplexityLabelExtension
open PlanarHom PlanarHom.Complexity
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding WeightedMaltsev MaltsevTypeStack
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension n : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Operation (Fin d)) (space : Polynomial ℕ)
variable (base : ComplexityTypeRowCallback.Context K) (W : StoredCode d n) (wanted : RowLabel K d)

theorem step_stored_shape (len : ℕ) (hlen : len≤n) (target : Tuple (Fin d) n) (b : Bool) :
    ∃len',∃target' : Tuple (Fin d) n,∃b',len'≤n ∧
      step L basis (curried m) space (storedState base W wanted len target b)=
        storedState base W wanted len' target' b' := by
  cases b with
  | false => exact ⟨len,target,false,hlen,step_dead L basis m space _ rfl⟩
  | true =>
    by_cases hl : len<n
    · cases hc : choose L basis (curried m) space (storedState base W wanted len target true) with
      | none =>
        refine ⟨len,target,false,hlen,?_⟩
        simp only [step,storedState,alive,context,ComplexityTypeStackConcrete.dimensionOf,
          ComplexityTypeStackConcrete.storedContext,ComplexityLabelExtension.len,ComplexityLabelExtension.target,
          ↓reduceIte]
        rw [if_pos hl]
        change (match choose L basis (curried m) space (storedState base W wanted len target true) with
          | none => _ | some _ => _)=_
        rw [hc]
      | some a =>
        have ha := choose_lt L basis (curried m) space hc
        let color : Fin d := ⟨a,ha⟩
        refine ⟨len+1,replaceCoordinate target ⟨len,hl⟩ color,true,by omega,?_⟩
        simp only [step,storedState,alive,context,ComplexityTypeStackConcrete.dimensionOf,
          ComplexityTypeStackConcrete.storedContext,ComplexityLabelExtension.len,ComplexityLabelExtension.target,
          ↓reduceIte]
        rw [if_pos hl]
        change (match choose L basis (curried m) space (storedState base W wanted len target true) with
          | none => _ | some _ => _)=_
        rw [hc]
        simp only []
        exact congrArg (fun t => (((base,n,rawTable W,maybeWord W.seed),wanted),len+1,t,true))
          (word_replaceCoordinate target ⟨len,hl⟩ color)
    · exact ⟨len,target,true,hlen,step_done L basis m space _ (by exact Nat.le_of_not_gt hl)⟩

theorem iterate_stored_shape (count len : ℕ) (hlen : len≤n) (target : Tuple (Fin d) n) (b : Bool) :
    ∃len',∃target' : Tuple (Fin d) n,∃b',len'≤n ∧
      (step L basis (curried m) space)^[count] (storedState base W wanted len target b)=
        storedState base W wanted len' target' b' := by
  induction count generalizing len target b with
  | zero => exact ⟨len,target,b,hlen,rfl⟩
  | succ count ih =>
    obtain ⟨len',target',b',hlen',hs⟩ := step_stored_shape L basis m space base W wanted len hlen target b
    rw [Function.iterate_succ_apply,hs]
    exact ih len' hlen' target' b'

theorem finish_stored_shape (len : ℕ) (hlen : len≤n) (target : Tuple (Fin d) n) (b : Bool)
    {result : List ℕ} (h : finish L (curried m) (storedState base W wanted len target b)=some result) :
    ∃x : Tuple (Fin d) n,word x=result := by
  cases b with
  | false => simp [finish,storedState,alive] at h
  | true =>
    change (ComplexityTypeStackConcrete.reconstruct (curried m)
      (ComplexityTypeStackConcrete.storedContext base W,len,word target)).filter
      (fun w => decide (ComplexityTypeStackConcrete.rowLabelOf L (curried m)
        (ComplexityTypeStackConcrete.storedContext base W,w)=wanted))=some result at h
    rw [ComplexityTypeStackConcrete.reconstruct_stored base m W target len hlen] at h
    have hr := (Option.filter_eq_some_iff.mp h).1
    obtain ⟨x,_,hx⟩ := Option.map_eq_some_iff.mp hr
    exact ⟨x,hx⟩

/-- Every successful public query on typed stored data returns a typed word,
even if a capped search chose arbitrary answers or failed elsewhere. -/
theorem extendQuery_stored_shape (len : ℕ) (hlen : len≤n) (target : Tuple (Fin d) n)
    {result : List ℕ}
    (h : extendQuery L basis (curried m) space
      (ComplexityTypeStackConcrete.storedContext base W,wanted,len,word target)=some result) :
    ∃x : Tuple (Fin d) n,word x=result := by
  obtain ⟨len',target',b',hlen',hs⟩ := iterate_stored_shape L basis m space base W wanted n len hlen target true
  change finish L (curried m) ((step L basis (curried m) space)^[n]
    (storedState base W wanted len target true))=some result at h
  rw [hs] at h
  exact finish_stored_shape L m base W wanted len' hlen' target' b' h

end ComplexCSP.ComplexityLabelExtension
