import Paper2.DegreeCSP.TwoWordContext
import Paper2.DegreeCSP.PartialUnaryProducts

/-! Exact incidence counts for the two-word context.  The degree receipt
retains every fixed pin and reversed disequality occurrence, so finite
products can impose the actual degree-cycle conditions on original values. -/
namespace Paper2.DegreeCSP.TwoWordContext
open scoped BigOperators
open Tractable TensorDecomposition
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

variable {n t : ℕ} (x y : Fin n → Bool)

def boundaryCount (t : ℕ) : ℕ :=
  Fintype.card {i : Fin n // Forward x y i} + t * Fintype.card (Reverse x y)

/-- The only boundary bit is used by each forward port once and by each
reversed port once for every literal disequality copy. -/
theorem boundary_degree (f : Signature AlgebraicComplex n) (t : ℕ) :
    (context x y f t).degree (Sum.inl 0)=boundaryCount x y t := by
  change (context x y f t).degree (OrderedPresentation.variableEquiv
    (H:=Hidden x y) (Sum.inl (0 : Fin 1)))=_
  rw [OrderedPresentation.ordered_degree]
  simp only [Fintype.sum_sum_type,arity]
  let : DecidableEq (Fin 1) := fun a b=>Classical.propDecidable (a=b)
  let : DecidableEq (Hidden x y) := fun a b=>Classical.propDecidable (a=b)
  have root : (∑ u : Unit,∑ i : Fin n, if scope x y (t:=t) (.inl u) i=Sum.inl (0 : Fin 1) then (1 : ℕ) else 0)=
      Fintype.card {i : Fin n // Forward x y i} := by
    simp only [scope,Fintype.sum_unique,root_boundary_iff]
    rw [Fintype.card_subtype,Finset.card_filter]
  have rev : (∑ p : Reverse x y × Fin t,∑ j : Fin 2,
      if scope x y (.inr (.inr p)) j=Sum.inl (0 : Fin 1) then (1 : ℕ) else 0)=
      t*Fintype.card (Reverse x y) := by
    simp [Fin.sum_univ_two,scope,Fintype.card_prod,Nat.mul_comm]
  have pin : (∑ p : Fixed x y × Fin t,∑ j : Fin 1,
      if scope x y (.inr (.inl p)) j=Sum.inl (0 : Fin 1) then (1 : ℕ) else 0)=0 := by
    simp only [scope,Sum.inr_ne_inl,ite_false,Finset.sum_const_zero]
  simpa only [boundaryCount,zero_add] using
    congrArg₂ (·+·) root (congrArg₂ (·+·) pin rev)

/-- The source port and exactly t fixed-pin or reversed-edge ports meet each
hidden variable. -/
theorem hidden_degree (f : Signature AlgebraicComplex n) (t : ℕ) (h : Hidden x y) :
    (context x y f t).degree (OrderedPresentation.variableEquiv (Sum.inr h))=t+1 := by
  rw [OrderedPresentation.ordered_degree]
  simp only [Fintype.sum_sum_type,arity]
  let : DecidableEq (Fin 1) := fun a b=>Classical.propDecidable (a=b)
  let : DecidableEq (Hidden x y) := fun a b=>Classical.propDecidable (a=b)
  have root : (∑ u : Unit,∑ i : Fin n,if scope x y (t:=t) (.inl u) i=Sum.inr h then (1 : ℕ) else 0)=1 := by
    simp only [scope,Fintype.sum_unique,root_hidden_iff]
    simp
  have pin : (∑ p : Fixed x y × Fin t,∑ j : Fin 1,
      if scope x y (.inr (.inl p)) j=Sum.inr h then (1 : ℕ) else 0)=
      if x h.val=y h.val then t else 0 := by
    simp only [Fintype.sum_prod_type,scope,Sum.inr.injEq,Subtype.ext_iff,
      Fintype.sum_unique]
    by_cases he:x h.val=y h.val
    · let v : Fixed x y := ⟨h.val,he⟩
      have eqv (p : Fixed x y) : p.val=h.val ↔ p=v := by
        simpa only [v] using (Subtype.ext_iff (a1:=p) (a2:=v)).symm
      simp only [eqv]
      simp [he]
    · have neq (p : Fixed x y) : p.val≠h.val := by
        intro hp
        exact he (hp ▸ p.property)
      simp [neq,he]
  have rev : (∑ p : Reverse x y × Fin t,∑ j : Fin 2,
      if scope x y (.inr (.inr p)) j=Sum.inr h then (1 : ℕ) else 0)=
      if x h.val=true ∧ y h.val=false then t else 0 := by
    simp only [Fintype.sum_prod_type,Fin.sum_univ_two,scope]
    have h10 : (1 : Fin 2)≠0 := by decide
    simp only [ite_true,h10,ite_false,Sum.inr.injEq,Subtype.ext_iff,
      Sum.inl_ne_inr,add_zero]
    by_cases he:x h.val=true ∧ y h.val=false
    · let v : Reverse x y := ⟨h.val,he⟩
      have eqv (p : Reverse x y) : p.val=h.val ↔ p=v := by
        simpa only [v] using (Subtype.ext_iff (a1:=p) (a2:=v)).symm
      simp only [eqv]
      simp [he]
    · have neq (p : Reverse x y) : p.val≠h.val := by
        intro hp
        exact he (hp ▸ p.property)
      simp [neq,he]
  rw [root,pin,rev]
  have hi := h.property
  cases hx:x h.val <;> cases hy:y h.val <;> simp_all [Forward]
  all_goals omega

/-- Hidden divisibility is unconditional; only the accumulated boundary
incidence is tested when contexts are multiplied. -/
theorem hidden_divisible (f : Signature AlgebraicComplex n) {k : ℕ} (hk : 0<k) :
    PartialUnaryProducts.HiddenDivisible (context x y f (k-1)) k := by
  intro h
  obtain ⟨w,hw⟩ := (Fintype.equivFin (Hidden x y)).surjective h
  subst h
  have he := hidden_degree x y f (k-1) w
  change k ∣ (context x y f (k-1)).degree (OrderedPresentation.variableEquiv (Sum.inr w))
  rw [he]
  have ht : k-1+1=k := by omega
  rw [ht]

end
end Paper2.DegreeCSP.TwoWordContext
