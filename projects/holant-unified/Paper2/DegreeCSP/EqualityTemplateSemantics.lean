import Paper2.DegreeCSP.EqualityTemplateWords

/-! Denotation of the deterministic, literally numbered equality templates.
No choice of a realization witness is used in these network constructors. -/
namespace Paper2.DegreeCSP.EqualityTemplates
open Paper2.ExactInput Paper2.Tractable
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

/-- Equality can be tested against any one of its occupied boundary ports. -/
theorem equality_at_port (n : ℕ) (x : Fin n → Bool) (i : Fin n) :
    equality (K := AlgebraicComplex) n x = if (∀ j, x j=x i) then 1 else 0 := by
  classical
  have hn : 0<n := by have hi := i.isLt; omega
  by_cases h : ∀ j, x j=x i
  · rw [if_pos h]
    have hx : x=(fun _ => x i) := funext h
    rw [hx]
    exact equality_constant n hn _
  · rw [if_neg h]
    by_contra hh
    obtain ⟨b,hb⟩ := equality_nonzero_constant n x hh
    exact h (fun j => (hb j).trans (hb i).symm)

/-- The named graph ports expose exactly the three local words. -/
theorem named_assignment {m k : ℕ} (hk : 3 ≤ k) (x : Boundary m k → Bool)
    (z : Edges m k → Bool) (v : Vertices m) :
    (fun j => Sum.elim x (fun p : Edges m k × Bool => if p.2 then !(z p.1) else z p.1)
      (namedPorts m k hk (v,j))) = row hk x z v := by
  funext j
  cases v with
  | inl t =>
    simp only [namedPorts,Equiv.coe_fn_mk,row,mainWord]
    split_ifs <;> simp_all
  | inr p =>
    rcases p with ⟨t,b⟩
    cases b
    · simp only [namedPorts,Equiv.coe_fn_mk,row,aWord]
      split_ifs <;> simp_all
    · rfl

/-- Native-X edge summation, reindexed by the literal arithmetic layout. -/
theorem positive_denote_formula (m k : ℕ) (hk : 3 ≤ k) (x : Fin (m*k) → Bool) :
    (positive m k hk).denote x =
      ∑ z : Edges m k → Bool, pathWeight hk (fun p => x (boundaryEquiv m k p)) z := by
  classical
  rw [Network.denote_nativeX _ (positive_nativeX m k hk)]
  trans (∑ z : Fin ((m-1)*k) → Bool, ∏ v : Fin (m+(m-1)*2),
    equality k (fun j => Sum.elim x
      (fun p : Fin ((m-1)*k) × Bool => if p.2 then !(z p.1) else z p.1)
        (positivePorts m k hk ⟨v,j⟩)))
  · apply Finset.sum_congr (by ext; simp)
    intro z _
    rfl
  let e : (Edges m k → Bool) ≃ (Fin ((m-1)*k) → Bool) :=
    Equiv.arrowCongr (edgeEquiv m k) (Equiv.refl Bool)
  rw [← e.sum_comp]
  apply Finset.sum_congr rfl
  intro z _
  unfold pathWeight
  rw [← (vertexEquiv m).prod_comp]
  apply Finset.prod_congr rfl
  intro v _
  change equality k (fun j => Sum.elim x
    (fun p : Fin ((m-1)*k) × Bool => if p.2 then !((e z) p.1) else (e z) p.1)
      (positivePorts m k hk ⟨vertexEquiv m v,j⟩)) = _
  congr 1
  rw [← named_assignment hk]
  funext j
  rw [positivePorts_named]
  cases namedPorts m k hk (v,j) with
  | inl p => rfl
  | inr p =>
    rcases p with ⟨q,b⟩
    change (if b then !((e z) (edgeEquiv m k q)) else (e z) (edgeEquiv m k q)) = _
    have he : (e z) (edgeEquiv m k q) = z q := by
      change z ((edgeEquiv m k).symm (edgeEquiv m k q)) = z q
      rw [Equiv.symm_apply_apply]
    rw [he]
    rfl

/-- The positive path has precisely one internal assignment for a constant
boundary word and none for a nonconstant boundary word. -/
theorem positive_denote (m k : ℕ) (hk : 3 ≤ k) (hm : 0<m) :
    (positive m k hk).denote = equality (m*k) := by
  classical
  funext x
  rw [positive_denote_formula]
  let xn : Boundary m k → Bool := fun p => x (boundaryEquiv m k p)
  let p : Boundary m k := (⟨0,hm⟩,two k hk)
  let b := xn p
  simp_rw [pathWeight_formula hk hm]
  have he : (∀ e, (fun _ : Edges m k => b) e=b) := fun _ => rfl
  have hzf : ∀ z : Edges m k → Bool, (∀ e, z e=b) ↔ z=(fun _ => b) :=
    fun z => ⟨fun h => funext h,fun h e => congrFun h e⟩
  change (∑ z : Edges m k → Bool, if (∀ q, xn q=b) ∧ (∀ e, z e=b) then 1 else 0) = _
  simp_rw [hzf]
  by_cases hx : ∀ q, xn q=b
  · simp only [and_iff_right hx,Finset.sum_ite_eq',Finset.mem_univ,if_true]
    rw [equality_at_port (m*k) x (boundaryEquiv m k p)]
    rw [if_pos]
    intro j
    simpa only [xn,b,Equiv.apply_symm_apply] using hx ((boundaryEquiv m k).symm j)
  · simp only [hx,false_and,if_false,Finset.sum_const_zero]
    rw [equality_at_port (m*k) x (boundaryEquiv m k p)]
    rw [if_neg]
    intro h
    apply hx
    intro q
    exact h (boundaryEquiv m k q)

/-- The fixed order of the two nullary rows contributes exactly two. -/
theorem nullary_denote (k : ℕ) (hk : 0<k) : (nullary k).denote = equality 0 := by
  classical
  funext x
  rw [Network.denote_nativeX _ (nullary_nativeX k)]
  trans (∑ z : Fin k → Bool, ∏ v : Fin 2,
    equality (K := AlgebraicComplex) k
      (fun j => if finTwoEquiv v then !(z j) else z j))
  · apply Finset.sum_congr (by ext; simp)
    intro z _
    rfl
  simp only [Fin.prod_univ_two]
  change (∑ z : Fin k → Bool, equality (K := AlgebraicComplex) k z *
    equality k (fun j => !(z j))) = _
  change (∑ z : Fin k → Bool, equality (K := AlgebraicComplex) k z *
    equality k (fun j => !(z j))) = equality 0 x
  simp_rw [equality_complement,Closed.equality_square k hk]
  rw [equality_zero]
  simp only [equality_eq,Finset.sum_add_distrib]
  norm_num

end
end Paper2.DegreeCSP.EqualityTemplates
