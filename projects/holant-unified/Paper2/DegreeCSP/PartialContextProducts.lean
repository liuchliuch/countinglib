import Paper2.DegreeCSP.PartialUnaryProducts

/-! Actual products of arbitrary-arity partial contexts. Each context keeps
its own hidden variables. The only boundary promise is the displayed finite
sum of occupied degrees, verified independently at every retained coordinate. -/
namespace Paper2.DegreeCSP.PartialContextProducts
open scoped BigOperators
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [CommSemiring K] {n k s : ℕ} {F : SignatureFamily K}

theorem generated (P : Fin s→Presentation K (Fin n)) (q : Fin s→ℕ)
    (uses : ∀i,(P i).Uses F)
    (hidden : ∀i,PartialUnaryProducts.HiddenDivisible (P i) k)
    (boundary : ∀j : Fin n,k∣∑i,q i*(P i).degree (Sum.inl j)) :
    Generated F k (fun x=>∏i,(P i).value x^(q i)) := by
  refine ⟨PartialUnaryProducts.product s P q,
    PartialUnaryProducts.product_uses s P q uses,?_,?_⟩
  · rintro (j | h)
    · rw [PartialUnaryProducts.product_boundary_degree]
      exact boundary j
    · exact PartialUnaryProducts.product_hidden_divisible_family s P q hidden h
  · exact funext (PartialUnaryProducts.product_value s P q)

theorem generated_of_degrees (P : Fin s→Presentation K (Fin n))
    (q : Fin s→ℕ) (d : Fin s→Fin n→ℕ)
    (uses : ∀i,(P i).Uses F)
    (hidden : ∀i,PartialUnaryProducts.HiddenDivisible (P i) k)
    (degree : ∀i j,(P i).degree (Sum.inl j)=d i j)
    (boundary : ∀j,k∣∑i,q i*d i j) :
    Generated F k (fun x=>∏i,(P i).value x^(q i)) := by
  apply generated P q uses hidden
  intro j
  simpa only [degree] using boundary j

/-- The two contexts may contain arbitrary different actual hidden sets.
Their literal product is generated once its boundary degrees add to multiples. -/
theorem generated_pair (P Q : Presentation K (Fin n))
    (usesP : P.Uses F) (usesQ : Q.Uses F)
    (hiddenP : PartialUnaryProducts.HiddenDivisible P k)
    (hiddenQ : PartialUnaryProducts.HiddenDivisible Q k)
    (boundary : ∀j,k∣P.degree (Sum.inl j)+Q.degree (Sum.inl j)) :
    Generated F k (fun x=>P.value x*Q.value x) := by
  refine ⟨P.disjointProduct Q,Presentation.product_uses P Q usesP usesQ,?_,?_⟩
  · rintro (j | h)
    · rw [Presentation.product_boundary_degree]
      exact boundary j
    · exact PartialUnaryProducts.product_hidden_divisible P Q hiddenP hiddenQ h
  · exact funext (Presentation.product_value P Q)

end
end Paper2.DegreeCSP.PartialContextProducts
