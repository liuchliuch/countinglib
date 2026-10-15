import Paper2.ExactInput.FixedRootCodec.Combinators

/-! Fixed finite candidate selection. Every test and every returned value is
computed by its supplied genuine finite program. The number of candidates is
part of the fixed field's program, not a runtime enumeration bound. -/
namespace Paper2.ExactInput.FixedRootCodec
open Computability Paper2.Complexity
open BinaryCompose FixedFieldMachines
noncomputable section

def firstVerified {B : Type} (fallback : B) : (m : ℕ) → (Fin m → Bool) → (Fin m → B) → B
  | 0, _, _ => fallback
  | m+1, test, value => if test 0 then value 0 else firstVerified fallback m (Fin.tail test) (Fin.tail value)

def firstVerifiedComputes {A B : Type} (ea : Encoding A Bool) (eb : Encoding B Bool)
    (fallback : B) : (m : ℕ) → (test : A → Fin m → Bool) → (value : A → Fin m → B) →
    (∀ i, Computes ea encodingBoolBool (fun x => test x i)) →
    (∀ i, Computes ea eb (fun x => value x i)) →
    Computes ea eb (fun x => firstVerified fallback m (test x) (value x))
  | 0, _, _, _, _ => constantComputes ea eb fallback
  | m+1, test, value, wt, wv => congrComputes
      (ifComputes (wt 0) (wv 0)
        (firstVerifiedComputes ea eb fallback m (fun x => Fin.tail (test x))
          (fun x => Fin.tail (value x)) (fun i => wt i.succ) (fun i => wv i.succ)))
      (fun _ => rfl)

theorem firstVerified_satisfies {B : Type} (fallback : B) (P : B → Prop) :
    ∀ (m : ℕ) (test : Fin m → Bool) (value : Fin m → B),
      (∀ i, test i=true → P (value i)) → (∃ i, test i=true) →
      P (firstVerified fallback m test value) := by
  intro m
  induction m with
  | zero => intro test value hall hex; obtain ⟨i,_⟩ := hex; exact Fin.elim0 i
  | succ m hm =>
    intro test value hall hex
    by_cases h : test 0=true
    · simpa only [firstVerified,h,ite_true] using hall 0 h
    · have ht : test 0=false := Bool.eq_false_iff.mpr h
      have hex' : ∃ i : Fin m, Fin.tail test i=true := by
        obtain ⟨i,hi⟩ := hex
        refine Fin.cases ?_ (fun j hj => ⟨j,hj⟩) i hi
        exact fun hi => (h hi).elim
      simpa only [firstVerified,ht,Bool.false_eq_true,ite_false] using
        hm (Fin.tail test) (Fin.tail value) (fun i => hall i.succ) hex'

end
end Paper2.ExactInput.FixedRootCodec
