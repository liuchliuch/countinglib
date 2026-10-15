import Paper2.MatchingPropagation.Support

namespace Paper2.MatchingPropagation
open CommonPhase EndpointSelfLoop
variable {ι : Type}

theorem product_coeff_literal (P : Matching ι) (p q : Fin P.count → ℂ)
    (c : ℂ) (x : ι → Bool) :
    product P p q c x =
      (c * ∏ j, if x (P.ports (j,false)) then q j else p j) * literal P ℂ x := by
  rw [literal_eq_prod]
  simp only [product,mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  cases x (P.ports (j,false)) <;> cases x (P.ports (j,true)) <;>
    simp [WeightedMatching.binary,bell_x_eq_indicator]

/-- If all other factors are literal, either surviving endpoint reads the
remaining oriented coefficient. This is an exact coefficient-table identity. -/
theorem product_single (P : Matching ι) (p q : Fin P.count → ℂ)
    (c : ℂ) (j : Fin P.count) (b : Bool) (hother : ∀ k, k ≠ j → p k = q k)
    (x : ι → Bool) :
    product P p q c x =
      (if x (P.ports (j,b)) = b then p j else q j) *
        (c * ∏ k ∈ Finset.univ.erase j, p k) * literal P ℂ x := by
  classical
  rw [product_coeff_literal]
  by_cases hx : Transversal P x
  · have hh : literal P ℂ x = 1 := by simp [literal,hx]
    rw [hh,mul_one,mul_one,← Finset.mul_prod_erase _ _ (Finset.mem_univ j)]
    have hprod : (∏ k ∈ Finset.univ.erase j, if x (P.ports (k,false)) then q k else p k) =
        ∏ k ∈ Finset.univ.erase j, p k := by
      apply Finset.prod_congr rfl
      intro k hk
      rw [← hother k (Finset.mem_erase.mp hk).1]
      split <;> rfl
    rw [hprod]
    have hj := hx j
    cases b <;> cases h₀ : x (P.ports (j,false)) <;>
      cases h₁ : x (P.ports (j,true)) <;> simp [h₀,h₁] at hj ⊢ <;> ring
  · simp [literal,hx]

theorem pairSum_single (P : Matching ι) (p q : Fin P.count → ℂ)
    (c : ℂ) (j : Fin P.count) (b : Bool) (hother : ∀ k, k ≠ j → p k = q k)
    (e : PortPair ι) (ha₁ : P.ports (j,b) ≠ e.first) (ha₂ : P.ports (j,b) ≠ e.second)
    (x : ι → Bool) :
    e.pairSum (product P p q c) x =
      (if x (P.ports (j,b)) = b then p j else q j) *
        ((c * ∏ k ∈ Finset.univ.erase j, p k) * e.pairSum (literal P ℂ) x) := by
  unfold PortPair.pairSum
  simp only [product_single P p q c j b hother,
    fill_other e x _ _ ha₁ ha₂,Finset.mul_sum,mul_assoc]

theorem pairSum_literal_complement (P : Matching ι) (e : PortPair ι) (x : ι → Bool) :
    e.pairSum (literal P ℂ) (fun a => !(x a)) = e.pairSum (literal P ℂ) x := by
  rw [PortPair.pairSum_eq_loop,PortPair.pairSum_eq_loop]
  change loop e.first e.second e.distinct (literal P ℂ)
      (fun a => !(restrict e.first e.second x a)) = _
  rw [← loop_complement]
  have hh : (fun y => literal P ℂ (fun i => !(y i))) = literal P ℂ :=
    funext (literal_complement P)
  rw [hh]

/-- The last possible non-X factor is forced to X even when the compared loop
hits one of its endpoints. A remaining endpoint fixes its coefficient, and
literal complement symmetry supplies the other coefficient without cancellation. -/
theorem single_factor_eq (P : Matching ι) (p q : Fin P.count → ℂ)
    (c : ℂ) (hp : ∀ j, p j ≠ 0) (hq : ∀ j, q j ≠ 0)
    (j : Fin P.count) (hother : ∀ k, k ≠ j → p k = q k)
    (e : PortPair ι) (b : Bool)
    (ha₁ : P.ports (j,b) ≠ e.first) (ha₂ : P.ports (j,b) ≠ e.second)
    (hnz : ∃ x, e.pairSum (product P p q c) x ≠ 0)
    (hflat : Flat (e.pairSum (product P p q c))) : p j = q j := by
  obtain ⟨x,hx⟩ := hnz
  let A := (c * ∏ k ∈ Finset.univ.erase j, p k) * e.pairSum (literal P ℂ) x
  have hA : A ≠ 0 := by
    intro hz
    apply hx
    rw [pairSum_single P p q c j b hother e ha₁ ha₂]
    change (if x (P.ports (j,b)) = b then p j else q j) * A = 0
    rw [hz,mul_zero]
  have hy : e.pairSum (product P p q c) (fun a => !(x a)) ≠ 0 := by
    rw [pairSum_single P p q c j b hother e ha₁ ha₂,pairSum_literal_complement]
    apply mul_ne_zero _ hA
    split <;> first | exact hp j | exact hq j
  have he := hflat x (fun a => !(x a)) hx hy
  rw [pairSum_single P p q c j b hother e ha₁ ha₂,
    pairSum_single P p q c j b hother e ha₁ ha₂,pairSum_literal_complement] at he
  have he' := mul_right_cancel₀ hA he
  generalize hw : x (P.ports (j,b)) = v at he'
  cases b <;> cases v <;> simp at he' <;> first | exact he' | exact he'.symm

end Paper2.MatchingPropagation
