import ComplexCSP.Instances.AllInstanceIsomorphism
import Mathlib.Data.Fintype.Quotient
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Exact recognition: assembling target isomorphisms from twin-class multiplicities

This is a finite structural step for an all-instance replacement theorem.
It makes no claim about equality on the paper's simple-instance class.
-/

set_option backward.isDefEq.respectTransparency false

namespace ComplexCSP.PinnedIsomorphism

section Twins

variable {A B K ι V : Type}
variable (L : Language A K ι)
variable (g : (i : ι) → (Fin (L.arity i) → B) → K)

/-- Twins form the exact coordinate-replacement equivalence relation. -/
def twinSetoid (L : Language A K ι) : Setoid A where
  r := L.Twins
  iseqv := ⟨L.twins_refl, fun h => L.twins_symm h, fun h h' => L.twins_trans h h'⟩

/-- A surjective target tuple lets an equal atomic diagram transfer source twins
into target twins, because it represents every possible coordinate context. -/
theorem twins_transfer_of_diagram (a : V → A) (b : V → B)
    (hdiag : SameAtomicDiagram L g a b) (hb : Function.Surjective b)
    {v w : V} (ht : L.Twins (a v) (a w)) : (L.retarget g).Twins (b v) (b w) := by
  classical
  intro i j x
  choose s hs using fun t => hb (x t)
  have he : b ∘ s = x := funext hs
  have hleft := hdiag i (Function.update s j v)
  have hright := hdiag i (Function.update s j w)
  rw [Function.comp_update, Function.comp_update, he] at hleft hright
  exact hleft.symm.trans ((ht i j (a ∘ s)).trans hright)

/-- With both tuples surjective, the atomic diagram identifies precisely the
same twin equivalence classes on their common index set. -/
theorem twins_iff_of_surjective_diagram (a : V → A) (b : V → B)
    (hdiag : SameAtomicDiagram L g a b)
    (ha : Function.Surjective a) (hb : Function.Surjective b) (v w : V) :
    L.Twins (a v) (a w) ↔ (L.retarget g).Twins (b v) (b w) := by
  constructor
  · exact twins_transfer_of_diagram L g a b hdiag hb
  · intro ht
    exact twins_transfer_of_diagram (L.retarget g) L.value b a
      (fun i s => (hdiag i s).symm) ha ht

/-- If a domain bijection carries every indexed pin into its matching twin class,
an equal surjective atomic diagram makes it an isomorphism of all tables. -/
theorem targetIso_of_diagram_and_pin_twins (a : V → A) (b : V → B)
    (hdiag : SameAtomicDiagram L g a b) (ha : Function.Surjective a)
    (e : A ≃ B) (hp : ∀ v, (L.retarget g).Twins (e (a v)) (b v)) :
    L.IsTargetIso g e := by
  classical
  intro i x
  choose s hs using fun t => ha (x t)
  have he : a ∘ s = x := funext hs
  rw [← he, hdiag]
  exact (L.retarget g).value_eq_of_twins i (b ∘ s) (e ∘ (a ∘ s))
    (fun j => (L.retarget g).twins_symm (hp (s j)))

/-- Structural assembly of an actual domain bijection. Exact cardinality equality
of corresponding twin classes is sufficient; arbitrary bijections inside those
classes are legitimate because every constraint is invariant under twins. -/
theorem targetIso_of_surjective_diagram_and_twin_card
    [Fintype A] [Fintype B]
    (a : V → A) (b : V → B) (hdiag : SameAtomicDiagram L g a b)
    (ha : Function.Surjective a) (hb : Function.Surjective b)
    (hcard : ∀ v, Nat.card {x : A // L.Twins x (a v)} =
      Nat.card {y : B // (L.retarget g).Twins y (b v)}) :
    ∃ e : A ≃ B, L.IsTargetIso g e ∧
      ∀ v, (L.retarget g).Twins (e (a v)) (b v) := by
  classical
  choose chooseA hchooseA using fun x => ha x
  let Q := Quotient (twinSetoid (L.retarget g))
  let qb : B → Q := Quotient.mk _
  let qa : A → Q := fun x => qb (b (chooseA x))
  have hfiber (v : V) (x : A) : qa x = qb (b v) ↔ L.Twins x (a v) := by
    change Quotient.mk _ (b (chooseA x)) = Quotient.mk _ (b v) ↔ _
    rw [Quotient.eq]
    change (L.retarget g).Twins (b (chooseA x)) (b v) ↔ _
    rw [← twins_iff_of_surjective_diagram L g a b hdiag ha hb]
    rw [hchooseA]
  have hcounts (q : Q) : Fintype.card {x : A // qa x = q} =
      Fintype.card {y : B // qb y = q} := by
    obtain ⟨y, rfl⟩ := Quotient.exists_rep q
    obtain ⟨v, rfl⟩ := hb y
    calc
      _ = Fintype.card {x : A // L.Twins x (a v)} :=
        Fintype.card_congr (Equiv.subtypeEquivRight (hfiber v))
      _ = Fintype.card {y : B // (L.retarget g).Twins y (b v)} := by
        simpa only [Nat.card_eq_fintype_card] using hcard v
      _ = _ := Fintype.card_congr (Equiv.subtypeEquivRight fun y => by
        change (twinSetoid (L.retarget g)).r y (b v) ↔
          @Quotient.mk B (twinSetoid (L.retarget g)) y =
            @Quotient.mk B (twinSetoid (L.retarget g)) (b v)
        exact Quotient.eq.symm)
  let fiberEquiv (q : Q) : {x : A // qa x = q} ≃ {y : B // qb y = q} :=
    Fintype.equivOfCardEq (hcounts q)
  let e : A ≃ B := Equiv.ofFiberEquiv fiberEquiv
  have hp : ∀ v, (L.retarget g).Twins (e (a v)) (b v) := by
    intro v
    have he : qb (e (a v)) = qa (a v) := Equiv.ofFiberEquiv_map fiberEquiv (a v)
    have hv : qa (a v) = qb (b v) := (hfiber v (a v)).mpr (L.twins_refl _)
    exact Quotient.exact (he.trans hv)
  exact ⟨e, targetIso_of_diagram_and_pin_twins L g a b hdiag ha e hp, hp⟩

end Twins

end ComplexCSP.PinnedIsomorphism
