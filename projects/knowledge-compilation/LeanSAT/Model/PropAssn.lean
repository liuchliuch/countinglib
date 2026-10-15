/- Independent assignment adapter for the target baseline.
The upstream module had no explicit license grant and is not copied. -/
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Tactic
namespace LeanSAT.Model
abbrev PropAssignment (ν : Type u) := ν → Bool
namespace PropAssignment
@[ext] theorem ext (a b : PropAssignment ν) (h : ∀ x, a x = b x) : a = b := funext h
def set [DecidableEq ν] (a : PropAssignment ν) (x : ν) (v : Bool) : PropAssignment ν :=
  Function.update (β := fun _ : ν => Bool) a x v
@[simp] theorem set_get [DecidableEq ν] (a : PropAssignment ν) (x : ν) (v : Bool) :
    a.set x v x = v := Function.update_self (β := fun _ : ν => Bool) x v a
theorem set_get_of_ne [DecidableEq ν] {x y : ν} (a : PropAssignment ν) (v : Bool) (h : x ≠ y) :
    a.set x v y = a y := Function.update_of_ne (β := fun _ : ν => Bool) h.symm v a
@[simp] theorem set_set [DecidableEq ν] (a : PropAssignment ν) (x : ν) (v v' : Bool) :
    (a.set x v).set x v' = a.set x v' := by
  funext y
  by_cases h : x = y
  · subst y; simp only [set_get]
  · simp only [set_get_of_ne _ _ h]
@[simp] theorem set_same [DecidableEq ν] (a : PropAssignment ν) (x : ν) :
    a.set x (a x) = a := Function.update_eq_self x a
def agreeOn (X : Set ν) (a b : PropAssignment ν) : Prop := ∀ x, x ∈ X → a x = b x
theorem agreeOn_refl (X : Set ν) (a : PropAssignment ν) : agreeOn X a a := fun _ _ => rfl
theorem agreeOn.symm : agreeOn X a b → agreeOn X b a := fun h x hx => (h x hx).symm
theorem agreeOn.trans : agreeOn X a b → agreeOn X b c → agreeOn X a c :=
  fun h k x hx => (h x hx).trans (k x hx)
theorem agreeOn.subset : X ⊆ Y → agreeOn Y a b → agreeOn X a b := fun hs h x hx => h x (hs hx)
theorem agreeOn_empty (a b : PropAssignment ν) : agreeOn ∅ a b := fun _ h => False.elim h
theorem agreeOn_set_of_not_mem [DecidableEq ν] {x : ν} {X : Set ν}
    (a : PropAssignment ν) (v : Bool) (hx : x ∉ X) : agreeOn X (a.set x v) a := by
  intro y hy
  exact set_get_of_ne a v (fun h => hx (h ▸ hy))
end PropAssignment
end LeanSAT.Model
