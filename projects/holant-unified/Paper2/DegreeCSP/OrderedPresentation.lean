import Paper2.DegreeCSP.Generated

/-! Exact finite enumeration of independently supplied constraint and hidden
variable types. Every occurrence is retained, and all proofs refer to the
literal degree-generated presentation used by the closed incidence compiler. -/
namespace Paper2.DegreeCSP
open scoped BigOperators
noncomputable section
namespace OrderedPresentation
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def variableEquiv {B H : Type} [Fintype H] : B ⊕ H ≃ B ⊕ Fin (Fintype.card H) :=
  Equiv.sumCongr (Equiv.refl B) (Fintype.equivFin H)

abbrev ordered {K B H J : Type} [Fintype H] [Fintype J]
    (a : J → ℕ) (f : (j : J) → Signature K (a j))
    (scope : (j : J) → Fin (a j) → B ⊕ H) : Presentation K B where
  hiddenCount := Fintype.card H
  constraints := Fintype.card J
  arity c := a ((Fintype.equivFin J).symm c)
  constraint c := f ((Fintype.equivFin J).symm c)
  scope c i := variableEquiv (scope ((Fintype.equivFin J).symm c) i)

theorem ordered_degree {K B H J : Type} [Fintype H] [Fintype J]
    (a : J → ℕ) (f : (j : J) → Signature K (a j))
    (scope : (j : J) → Fin (a j) → B ⊕ H) (v : B ⊕ H) :
    (ordered a f scope).degree (variableEquiv v) =
      ∑ j, ∑ i, if scope j i = v then 1 else 0 := by
  classical
  change Nat.card ((ordered a f scope).Fiber (variableEquiv v)) = _
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,
    Finset.card_filter,Fintype.sum_sigma]
  dsimp only [Presentation.route,ordered]
  have he (u w : B ⊕ H) : variableEquiv u = variableEquiv w ↔ u = w :=
    (variableEquiv : B ⊕ H ≃ B ⊕ Fin (Fintype.card H)).injective.eq_iff
  simp only [he]
  exact (Fintype.equivFin J).symm.sum_comp
    (fun j => ∑ i, if scope j i = v then 1 else 0)

theorem ordered_uses {K B H J : Type} [Fintype H] [Fintype J]
    (a : J → ℕ) (f : (j : J) → Signature K (a j))
    (scope : (j : J) → Fin (a j) → B ⊕ H) (F : SignatureFamily K)
    (h : ∀ j, (⟨a j,f j⟩ : AnySignature K) ∈ F) : (ordered a f scope).Uses F :=
  fun c => h ((Fintype.equivFin J).symm c)

theorem ordered_value {K B H J : Type} [CommSemiring K] [Fintype H] [Fintype J]
    (a : J → ℕ) (f : (j : J) → Signature K (a j))
    (scope : (j : J) → Fin (a j) → B ⊕ H) (x : B → Bool) :
    (ordered a f scope).value x =
      ∑ y : H → Bool, ∏ j, f j (fun i => Sum.elim x y (scope j i)) := by
  classical
  let e : (Fin (Fintype.card H) → Bool) ≃ (H → Bool) :=
    Equiv.arrowCongr (Fintype.equivFin H).symm (Equiv.refl Bool)
  unfold Presentation.value
  apply Fintype.sum_equiv e
  intro y
  have hp := (Fintype.equivFin J).symm.prod_comp
    (fun j => f j (fun i => Sum.elim x (e y) (scope j i)))
  rw [← hp]
  apply Finset.prod_congr rfl
  intro c _
  congr 1
  funext i
  change Sum.elim x y (variableEquiv (scope ((Fintype.equivFin J).symm c) i)) =
    Sum.elim x (e y) (scope ((Fintype.equivFin J).symm c) i)
  cases scope ((Fintype.equivFin J).symm c) i <;>
    simp [variableEquiv,e,Equiv.arrowCongr]

end OrderedPresentation
end
end Paper2.DegreeCSP
