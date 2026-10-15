import ComplexCSP.Complexity.LabelExtensionBounds
import ComplexCSP.Structure.MaltsevTypeMarginalRestrictedExecution
import ComplexCSP.Structure.MaltsevTypeWitness

set_option backward.isDefEq.respectTransparency false

/-! # Exact greedy-extension correspondence on actual restricted marginal contexts -/
namespace ComplexCSP.ComplexityLabelExtension
open PlanarHom PlanarHom.Complexity
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding WeightedMaltsev
open ComplexityWitnessPrimitives MaltsevTypeStack
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Operation (Fin d)) (space : Polynomial ℕ)
local instance (priority := 2000) : BEq (RowLabel K d) := instBEqOfDecidableEq
local instance (priority := 2000) : LawfulBEq (RowLabel K d) := inferInstance

abbrev curried (m : Operation (Fin d)) := fun a b c => m (a,b,c)

def storedState {n : ℕ} (base : ComplexityTypeRowCallback.Context K) (W : StoredCode d n)
    (wanted : RowLabel K d) (len : ℕ) (target : Tuple (Fin d) n) (alive : Bool) : State K d :=
  ((ComplexityTypeStackConcrete.storedContext base W,wanted),len,word target,alive)

theorem step_dead (p : State K d) (h : alive p=false) : step L basis (curried m) space p=p := by
  simp only [step,h,Bool.false_eq_true,↓reduceIte]

theorem step_done (p : State K d) (h : ComplexityTypeStackConcrete.dimensionOf (context p)≤len p) :
    step L basis (curried m) space p=p := by
  simp only [step,not_lt.mpr h,↓reduceIte,ite_self]

theorem iterate_stops (count : ℕ) (p : State K d)
    (h : ComplexityTypeStackConcrete.dimensionOf (context p)≤len p+count) :
    step L basis (curried m) space ((step L basis (curried m) space)^[count] p)=
      (step L basis (curried m) space)^[count] p := by
  induction count generalizing p with
  | zero => exact step_done L basis m space p (by simpa using h)
  | succ count ih =>
    by_cases ha : alive p=true
    · by_cases hl : len p<ComplexityTypeStackConcrete.dimensionOf (context p)
      · rw [Function.iterate_succ_apply]
        cases hc : choose L basis (curried m) space p with
        | none =>
          have hs : step L basis (curried m) space p=(p.1,len p,target p,false) := by simp [step,ha,hl,hc]
          rw [hs]
          have hd := step_dead L basis m space (p.1,len p,target p,false) rfl
          rw [Function.iterate_fixed hd]
          exact hd
        | some a =>
          have hs : step L basis (curried m) space p=(p.1,len p+1,replaceAt (target p) (len p) a,true) := by
            simp [step,ha,hl,hc]
          rw [hs]
          apply ih
          change ComplexityTypeStackConcrete.dimensionOf (context p)≤len p+1+count
          omega
      · have hd := step_done L basis m space p (Nat.le_of_not_gt hl)
        rw [Function.iterate_fixed hd]
        exact hd
    · have hd := step_dead L basis m space p (Bool.eq_false_iff.mpr ha)
      rw [Function.iterate_fixed hd]
      exact hd

section Stored
variable {n : ℕ} (base : ComplexityTypeRowCallback.Context K) (W : StoredCode d n)
variable (label : Tuple (Fin d) n → RowLabel K d)
variable (hlab : ∀x,ComplexityTypeStackConcrete.rowLabelOf L (curried m)
  (ComplexityTypeStackConcrete.storedContext base W,word x)=label x)
variable (hquery : ∀fuel len,len+fuel=n → ∀target : Tuple (Fin d) n,
  (ComplexityTypeQuery.executeWithSpace L basis (curried m) space
    (ComplexityTypeStackConcrete.storedContext base W,len,word target)).1=
    (materializedTypeSearch m W.toCode label fuel len target []).1)

include hlab in
theorem finish_stored (wanted : RowLabel K d) (len : ℕ) (hlen : len≤n) (target : Tuple (Fin d) n) :
    finish L (curried m) (storedState base W wanted len target true)=
      ((reconstructTo m W.toCode target len).filter (fun x => label x == wanted)).map word := by
  change (ComplexityTypeStackConcrete.reconstruct (curried m)
      (ComplexityTypeStackConcrete.storedContext base W,len,word target)).filter
      (fun w => decide (ComplexityTypeStackConcrete.rowLabelOf L (curried m)
        (ComplexityTypeStackConcrete.storedContext base W,w)=wanted))=_
  rw [ComplexityTypeStackConcrete.reconstruct_stored base m W target len hlen]
  cases hr : reconstructTo m W.toCode target len with
  | none => rfl
  | some x =>
    simp only [Option.map_some,Option.filter,hlab]
    by_cases he : label x=wanted <;> simp [he]

include hquery in
theorem choose_stored (wanted : RowLabel K d) (fuel len : ℕ) (hdepth : len+(fuel+1)=n)
    (target : Tuple (Fin d) n) :
    choose L basis (curried m) space (storedState base W wanted len target true)=
      ((List.finRange d).find? (fun a => decide (wanted ∈
        (materializedTypeSearch m W.toCode label fuel (len+1)
          (replaceCoordinate target ⟨len,by omega⟩ a) []).1))).map Fin.val := by
  unfold choose candidates
  rw [List.head?_filter]
  have hr : (List.finRange d).map Fin.val=List.range d := by simp
  rw [←hr,List.find?_map]
  congr 2
  funext a
  apply Bool.eq_iff_iff.mpr
  simp only [Function.comp_apply,accepts,storedState,context,ComplexityLabelExtension.len,ComplexityLabelExtension.target,ComplexityLabelExtension.wanted,decide_eq_true_eq]
  rw [word_replaceCoordinate target ⟨len,by omega⟩ a,hquery fuel (len+1) (by omega)]

include hquery hlab in
theorem execute_stored (wanted : RowLabel K d) (fuel len : ℕ) (hdepth : len+fuel=n)
    (target : Tuple (Fin d) n) :
    execute L basis (curried m) space (fuel,storedState base W wanted len target true)=
      (labelExtension m W.toCode label wanted fuel len target).map word := by
  induction fuel generalizing len target with
  | zero =>
    exact finish_stored L m base W label hlab wanted len (by omega) target
  | succ fuel ih =>
    have hl : len<n := by omega
    have hc := choose_stored L basis m space base W label hquery wanted fuel len hdepth target
    unfold execute
    rw [Function.iterate_succ_apply]
    rw [labelExtension,dif_pos hl]
    cases ha : (List.finRange d).find? (fun a => decide (wanted ∈
      (materializedTypeSearch m W.toCode label fuel (len+1)
        (replaceCoordinate target ⟨len,hl⟩ a) []).1)) with
    | none =>
      rw [ha,Option.map_none] at hc
      have hs : step L basis (curried m) space (storedState base W wanted len target true)=
          storedState base W wanted len target false := by
        simp only [step,storedState,alive,context,ComplexityTypeStackConcrete.dimensionOf,
          ComplexityTypeStackConcrete.storedContext,↓reduceIte,ComplexityLabelExtension.len,ComplexityLabelExtension.target]
        rw [if_pos hl]
        change (match choose L basis (curried m) space (storedState base W wanted len target true) with
          | none => _ | some _ => _) = _
        rw [hc]
      rw [hs,Function.iterate_fixed (step_dead L basis m space _ rfl)]
      simp [finish,storedState,alive]
    | some a =>
      rw [ha,Option.map_some] at hc
      have hs : step L basis (curried m) space (storedState base W wanted len target true)=
          storedState base W wanted (len+1) (replaceCoordinate target ⟨len,hl⟩ a) true := by
        simp only [step,storedState,alive,context,ComplexityTypeStackConcrete.dimensionOf,
          ComplexityTypeStackConcrete.storedContext,↓reduceIte,ComplexityLabelExtension.len,ComplexityLabelExtension.target]
        rw [if_pos hl]
        change (match choose L basis (curried m) space (storedState base W wanted len target true) with
          | none => _ | some _ => _) = _
        rw [hc]
        simp only []
        rw [word_replaceCoordinate target ⟨len,hl⟩ a]
      rw [hs]
      exact ih (len+1) (by omega) _

include hquery hlab in
theorem extendQuery_stored (wanted : RowLabel K d) (fuel len : ℕ) (hdepth : len+fuel=n)
    (target : Tuple (Fin d) n) :
    extendQuery L basis (curried m) space
      (ComplexityTypeStackConcrete.storedContext base W,wanted,len,word target)=
      (labelExtension m W.toCode label wanted fuel len target).map word := by
  have hs := iterate_stops L basis m space fuel (storedState base W wanted len target true)
    (by change n≤len+fuel; omega)
  change finish L (curried m) ((step L basis (curried m) space)^[n]
      (storedState base W wanted len target true))=_
  have he := congrArg (fun k => (step L basis (curried m) space)^[k]
    (storedState base W wanted len target true)) hdepth.symm
  rw [he,Function.iterate_add_apply,Function.iterate_fixed hs]
  exact execute_stored L basis m space base W label hlab hquery wanted fuel len hdepth target

end Stored
end ComplexCSP.ComplexityLabelExtension
