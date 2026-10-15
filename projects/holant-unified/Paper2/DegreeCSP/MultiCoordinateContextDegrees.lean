import Paper2.DegreeCSP.MultiCoordinateContext

/-! Exact occupied degrees for original multi-coordinate contexts. Hidden
ports retain the source occurrence and all t actual pin or X occurrences. -/
namespace Paper2.DegreeCSP.MultiCoordinateContext
open scoped BigOperators
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable
variable {n r t : ℕ} (E : Fin n→Expr r)

def boundaryWeight (t : ℕ) (j : Fin r) : ℕ :=
  ∑i,if E i=Sum.inr (j,false) then 1 else if E i=Sum.inr (j,true) then t else 0

private theorem fixed_hidden_iff (p : Fixed E) (h : Hidden E) (u : Fin t) (j : Fin 1) :
    scope E (.inr (.inl (p,u))) j=Sum.inr h ↔ p.val.1=h.val := by
  simp only [scope,Sum.inr.injEq,Subtype.ext_iff]

private theorem reverse_hidden_count (p : Reverse E) (h : Hidden E) (u : Fin t) :
    (∑l:Fin 2,if scope E (.inr (.inr (p,u))) l=Sum.inr h then (1:ℕ) else 0)=
      if p.val.1=h.val then 1 else 0 := by
  rw [Fin.sum_univ_two]
  simp [scope,Subtype.ext_iff]

private theorem reverse_boundary_count (p : Reverse E) (j : Fin r) (u : Fin t) :
    (∑l:Fin 2,if scope E (.inr (.inr (p,u))) l=Sum.inl j then (1:ℕ) else 0)=
      if p.val.2=j then 1 else 0 := by
  rw [Fin.sum_univ_two]
  simp [scope]

private theorem reverse_port_sum (i : Fin n) (j : Fin r) (t : ℕ) :
    (∑p:Reverse E,if p.val.1=i ∧ p.val.2=j then t else 0)=
      if E i=Sum.inr (j,true) then t else 0 := by
  by_cases hi:E i=Sum.inr (j,true)
  · let v : Reverse E:=⟨(i,j),hi⟩
    have he (p : Reverse E) : p.val.1=i ∧ p.val.2=j ↔ p=v := by
      exact ⟨fun h=>Subtype.ext (Prod.ext h.1 h.2),fun h=>by subst p;exact ⟨rfl,rfl⟩⟩
    simp [he,hi]
  · have hn (p : Reverse E) : ¬(p.val.1=i ∧ p.val.2=j) := by
      rintro ⟨h1,h2⟩
      exact hi (by simpa only [h1,h2] using p.property)
    simp [hn,hi]

private theorem reverse_boundary_sum (j : Fin r) (t : ℕ) :
    (∑p:Reverse E×Fin t,∑l:Fin 2,
      if scope E (.inr (.inr p)) l=Sum.inl j then (1:ℕ) else 0)=
      ∑i:Fin n,if E i=Sum.inr (j,true) then t else 0 := by
  simp only [Fintype.sum_prod_type,reverse_boundary_count]
  have hcount (p : Reverse E) :
      (∑u:Fin t,if p.val.2=j then (1:ℕ) else 0)=if p.val.2=j then t else 0 := by
    by_cases hj:p.val.2=j <;> simp [hj]
  simp only [hcount]
  have he (p : Reverse E) : (if p.val.2=j then t else 0)=
      ∑i:Fin n,if p.val.1=i ∧ p.val.2=j then t else 0 := by
    by_cases hj:p.val.2=j <;> simp [hj]
  simp_rw [he]
  rw [Finset.sum_comm]
  simp only [reverse_port_sum]

theorem boundary_degree (f : Signature AlgebraicComplex n) (t : ℕ) (j : Fin r) :
    (context E f t).degree (Sum.inl j)=boundaryWeight E t j := by
  change (context E f t).degree (OrderedPresentation.variableEquiv
    (H:=Hidden E) (Sum.inl j))=_
  rw [OrderedPresentation.ordered_degree]
  simp only [Fintype.sum_sum_type,arity,Fintype.sum_unique]
  have root : (∑i:Fin n,if rootScope E i=Sum.inl j then (1:ℕ) else 0)=
      ∑i:Fin n,if E i=Sum.inr (j,false) then 1 else 0 := by
    simp only [root_boundary_iff]
  convert_to (∑i:Fin n,if rootScope E i=Sum.inl j then (1:ℕ) else 0)+
    ((∑p:Fixed E×Fin t,if scope E (.inr (.inl p)) (0:Fin 1)=Sum.inl j then (1:ℕ) else 0)+
    (∑p:Reverse E×Fin t,∑l:Fin 2,
      if scope E (.inr (.inr p)) l=Sum.inl j then (1:ℕ) else 0))=boundaryWeight E t j using 1
  · simp only [scope]
    apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hi:rootScope E i=Sum.inl j <;> simp [hi]
    · apply congrArg₂ (·+·)
      · simp
      · apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro l _
        by_cases hl:l=0 <;> by_cases hj:p.1.val.2=j <;> simp [hl,hj]
  have pins : (∑p:Fixed E×Fin t,if scope E (.inr (.inl p)) (0:Fin 1)=Sum.inl j then (1:ℕ) else 0)=0 := by
    simp [scope]
  rw [root,pins,zero_add,reverse_boundary_sum]
  unfold boundaryWeight
  rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi:E i=Sum.inr (j,false)
  · simp [hi]
  · simp [hi]

theorem hidden_degree (f : Signature AlgebraicComplex n) (t : ℕ) (h : Hidden E) :
    (context E f t).degree (OrderedPresentation.variableEquiv (Sum.inr h))=t+1 := by
  rw [OrderedPresentation.ordered_degree]
  simp only [Fintype.sum_sum_type,arity,Fintype.sum_unique]
  have root : (∑i:Fin n,if rootScope E i=Sum.inr h then (1:ℕ) else 0)=1 := by
    simp only [root_hidden_iff]
    simp
  convert_to (∑i:Fin n,if rootScope E i=Sum.inr h then (1:ℕ) else 0)+
    ((∑p:Fixed E×Fin t,∑l:Fin 1,
      if scope E (.inr (.inl p)) l=Sum.inr h then (1:ℕ) else 0)+
    (∑p:Reverse E×Fin t,∑l:Fin 2,
      if scope E (.inr (.inr p)) l=Sum.inr h then (1:ℕ) else 0))=t+1 using 1
  · simp only [scope,Fintype.sum_unique]
    apply congrArg₂ (·+·)
    · apply Finset.sum_congr rfl
      intro i _
      by_cases hi:rootScope E i=Sum.inr h <;> simp [hi]
    · apply congrArg₂ (·+·)
      · apply Finset.sum_congr rfl
        intro p _
        by_cases hp:p.1.val.1=h.val <;> simp [Subtype.ext_iff,hp]
      · apply Finset.sum_congr rfl
        intro p _
        apply Finset.sum_congr rfl
        intro l _
        by_cases hl:l=0 <;> by_cases hp:p.1.val.1=h.val <;> simp [hl,Subtype.ext_iff,hp]
  rw [root]
  simp only [Fintype.sum_prod_type,Fintype.sum_unique,reverse_hidden_count,
    scope,Sum.inr.injEq,Subtype.ext_iff]
  cases hi:E h.val with
  | inl b=>
    let v : Fixed E:=⟨(h.val,b),hi⟩
    have he (p : Fixed E) : p.val.1=h.val ↔ p=v := by
      constructor
      · intro hp
        apply Subtype.ext
        apply Prod.ext hp
        have H:=p.property
        rw [hp,hi] at H
        exact (Sum.inl.inj H).symm
      · intro hp;subst p;rfl
    have hn (p : Reverse E) : p.val.1≠h.val := by
      intro hp
      have H:=p.property
      rw [hp,hi] at H
      cases H
    simp [he,hn,Nat.add_comm]
  | inr p=>
    rcases p with ⟨j,b⟩
    cases b
    · exact False.elim (h.property ⟨j,hi⟩)
    · let v : Reverse E:=⟨(h.val,j),hi⟩
      have he (p : Reverse E) : p.val.1=h.val ↔ p=v := by
        constructor
        · intro hp
          apply Subtype.ext
          apply Prod.ext hp
          have H:=p.property
          rw [hp,hi] at H
          exact (Prod.mk.inj (Sum.inr.inj H)).1.symm
        · intro hp;subst p;rfl
      have hn (p : Fixed E) : p.val.1≠h.val := by
        intro hp
        have H:=p.property
        rw [hp,hi] at H
        cases H
      simp [he,hn,Nat.add_comm]

/-- Hidden divisibility follows from the exact completed occupied degree;
the boundary degrees are retained for the separate degree-cycle test. -/
theorem hidden_divisible (f : Signature AlgebraicComplex n) {k : ℕ} (t : ℕ)
    (hd : k∣t+1) : PartialUnaryProducts.HiddenDivisible (context E f t) k := by
  intro h
  obtain ⟨w,hw⟩ := (Fintype.equivFin (Hidden E)).surjective h
  subst h
  change k∣(context E f t).degree (OrderedPresentation.variableEquiv (Sum.inr w))
  rw [hidden_degree]
  exact hd

end
end Paper2.DegreeCSP.MultiCoordinateContext
