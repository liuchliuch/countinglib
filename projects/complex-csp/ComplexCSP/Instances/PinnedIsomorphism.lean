import ComplexCSP.Instances.Basic
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Basic

/-! # Finite target isomorphism and pin twins

These definitions and soundness lemmas implement the finite candidate checker.
IsomorphismCompleteness proves its completeness for all finite instances. -/
namespace ComplexCSP

namespace Language
variable {A B K ι : Type}

/-- A target family with the same symbol arities and different domain/tables. -/
def retarget (L : Language A K ι)
    (g : (i : ι) → (Fin (L.arity i) → B) → K) : Language B K ι where
  arity := L.arity
  arity_pos := L.arity_pos
  value := g

/-- Twins may replace one coordinate in every context of every signature. -/
def Twins (L : Language A K ι) (a b : A) : Prop :=
  ∀ i (j : Fin (L.arity i)) (x : Fin (L.arity i) → A),
    L.value i (Function.update x j a) = L.value i (Function.update x j b)

@[refl] theorem twins_refl (L : Language A K ι) (a : A) : L.Twins a a :=
  fun _ _ _ => rfl

@[symm] theorem twins_symm (L : Language A K ι) {a b : A}
    (h : L.Twins a b) : L.Twins b a := fun i j x => (h i j x).symm

@[trans] theorem twins_trans (L : Language A K ι) {a b c : A}
    (hab : L.Twins a b) (hbc : L.Twins b c) : L.Twins a c :=
  fun i j x => (hab i j x).trans (hbc i j x)

/-- An actual domain bijection carrying every indexed table to its counterpart. -/
def IsTargetIso (L : Language A K ι)
    (g : (i : ι) → (Fin (L.arity i) → B) → K) (e : A ≃ B) : Prop :=
  ∀ i (x : Fin (L.arity i) → A), L.value i x = g i (e ∘ x)

/-- Coordinatewise twin replacements preserve every full constraint value. -/
theorem value_eq_of_twins (L : Language A K ι) (i : ι)
    (x y : Fin (L.arity i) → A) (h : ∀ j, L.Twins (x j) (y j)) :
    L.value i x = L.value i y := by
  classical
  have step : ∀ s : Finset (Fin (L.arity i)),
      L.value i x = L.value i (fun j => if j ∈ s then y j else x j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hjs ih =>
      let z : Fin (L.arity i) → A := fun k => if k ∈ s then y k else x k
      have hx : Function.update z j (x j) = z := by
        funext k
        by_cases hkj : k = j
        · subst k
          simp [z, hjs]
        · simp [Function.update_of_ne hkj]
      have hy : Function.update z j (y j) =
          (fun k => if k ∈ insert j s then y k else x k) := by
        funext k
        by_cases hkj : k = j
        · subst k
          simp
        · simp [Finset.mem_insert, hkj, z]
      have hv := h j i j z
      rw [hx, hy] at hv
      exact ih.trans hv
  simpa using step Finset.univ

end Language

namespace Instance
variable {A B K ι V H : Type} {L : Language A K ι}

/-- Reinterpret the same finite labelled instance using arity-matched target
functions. Every occurrence, repeated scope, boundary label and hidden variable
is retained literally. -/
def retarget (I : Instance L V H)
    (g : (i : ι) → (Fin (L.arity i) → B) → K) : Instance (L.retarget g) V H :=
  ⟨I.constraints.map (fun c => ⟨c.symbol, c.scope⟩)⟩

/-- A domain isomorphism preserves the weight of each individual assignment. -/
theorem eval_retarget_iso [CommMonoid K]
    (I : Instance L V H) (g : (i : ι) → (Fin (L.arity i) → B) → K)
    (e : A ≃ B) (he : L.IsTargetIso g e) (a : V → A) (b : H → A) :
    I.eval a b = (I.retarget g).eval (e ∘ a) (e ∘ b) := by
  unfold eval retarget
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  change L.value c.symbol (Sum.elim a b ∘ c.scope) =
    g c.symbol (Sum.elim (e ∘ a) (e ∘ b) ∘ c.scope)
  rw [he]
  congr 1
  funext j
  cases hscope : c.scope j <;> simp [Function.comp_apply, hscope]

/-- Fixed-label twin replacements preserve each assignment weight, including
when a boundary variable occurs repeatedly inside one constraint. -/
theorem eval_eq_of_pin_twins [CommMonoid K] (I : Instance L V H)
    (a a' : V → A) (ha : ∀ v, L.Twins (a v) (a' v)) (b : H → A) :
    I.eval a b = I.eval a' b := by
  unfold eval
  congr 1
  apply List.map_congr_left
  intro c _
  apply L.value_eq_of_twins c.symbol
  intro j
  change L.Twins (Sum.elim a b (c.scope j)) (Sum.elim a' b (c.scope j))
  cases hscope : c.scope j with
  | inl v => simpa only [hscope, Sum.elim_inl] using ha v
  | inr v => exact L.twins_refl (b v)

/-- Pinned partition values are invariant under twin replacement. -/
theorem partition_eq_of_pin_twins [CommSemiring K] [Fintype A] [Fintype H]
    [DecidableEq H] (I : Instance L V H)
    (a a' : V → A) (ha : ∀ v, L.Twins (a v) (a' v)) :
    I.partition a = I.partition a' := by
  unfold partition
  apply Finset.sum_congr rfl
  intro b _
  exact I.eval_eq_of_pin_twins a a' ha b

/-- An actual bijective change of target domain preserves every pinned sum. -/
theorem partition_retarget_iso [CommSemiring K] [Fintype A] [Fintype B]
    [Fintype H] [DecidableEq H]
    (I : Instance L V H) (g : (i : ι) → (Fin (L.arity i) → B) → K)
    (e : A ≃ B) (he : L.IsTargetIso g e) (a : V → A) :
    I.partition a = (I.retarget g).partition (e ∘ a) := by
  unfold partition
  exact Fintype.sum_equiv (Equiv.piCongrRight fun _ : H => e)
    (I.eval a) ((I.retarget g).eval (e ∘ a))
    (fun b => I.eval_retarget_iso g e he a b)

/-- The complete soundness direction of Theorem 5.2: an isomorphism up to pin
twins suffices for equality on all finite instances, with no simplicity promise. -/
theorem partition_eq_of_iso_pin_twins [CommSemiring K] [Fintype A] [Fintype B]
    [Fintype H] [DecidableEq H]
    (I : Instance L V H) (g : (i : ι) → (Fin (L.arity i) → B) → K)
    (e : A ≃ B) (he : L.IsTargetIso g e) (a : V → A) (b : V → B)
    (hp : ∀ v, (L.retarget g).Twins (e (a v)) (b v)) :
    I.partition a = (I.retarget g).partition b :=
  (I.partition_retarget_iso g e he a).trans
    ((I.retarget g).partition_eq_of_pin_twins (e ∘ a) b hp)

end Instance
namespace Language
variable {A B K ι V : Type}

instance decidableTwins [Fintype A] [Fintype ι] [DecidableEq K]
    (L : Language A K ι) (a b : A) : Decidable (L.Twins a b) :=
  inferInstanceAs (Decidable (∀ i (j : Fin (L.arity i)) (x : Fin (L.arity i) → A),
    L.value i (Function.update x j a) = L.value i (Function.update x j b)))

instance decidableTargetIso [Fintype A] [Fintype ι] [DecidableEq K]
    (L : Language A K ι) (g : (i : ι) → (Fin (L.arity i) → B) → K)
    (e : A ≃ B) : Decidable (L.IsTargetIso g e) :=
  inferInstanceAs (Decidable (∀ i (x : Fin (L.arity i) → A), L.value i x = g i (e ∘ x)))

/-- Enumerate all finite domain bijections and test the exact table and pin-twin
conditions. This decides the finite isomorphism criterion, not universal CSP
equality until the separate Young completeness theorem has been proved. -/
def pinnedIsoCheck [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Fintype ι] [Fintype V] [DecidableEq K]
    (L : Language A K ι) (g : (i : ι) → (Fin (L.arity i) → B) → K)
    (a : V → A) (b : V → B) : Bool :=
  decide (∃ e : A ≃ B, L.IsTargetIso g e ∧ ∀ v, (L.retarget g).Twins (e (a v)) (b v))

theorem pinnedIsoCheck_eq_true [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Fintype ι] [Fintype V] [DecidableEq K]
    (L : Language A K ι) (g : (i : ι) → (Fin (L.arity i) → B) → K)
    (a : V → A) (b : V → B) :
    L.pinnedIsoCheck g a b = true ↔
      ∃ e : A ≃ B, L.IsTargetIso g e ∧ ∀ v, (L.retarget g).Twins (e (a v)) (b v) := by
  simp only [pinnedIsoCheck, decide_eq_true_eq]

/-- Every accepted finite candidate gives equal pinned values on all actual
finite instances, with repeated scopes, arbitrary hidden variables, and isolated
variables. This theorem does not assume the desired partition equality. -/
theorem pinnedIsoCheck_sound [CommSemiring K]
    [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [Fintype ι] [Fintype V] [DecidableEq K]
    (L : Language A K ι) (g : (i : ι) → (Fin (L.arity i) → B) → K)
    (a : V → A) (b : V → B) (hc : L.pinnedIsoCheck g a b = true)
    {H : Type} [Fintype H] [DecidableEq H] (I : Instance L V H) :
    I.partition a = (I.retarget g).partition b := by
  obtain ⟨e, he, hp⟩ := (pinnedIsoCheck_eq_true L g a b).mp hc
  exact I.partition_eq_of_iso_pin_twins g e he a b hp
end Language
end ComplexCSP
