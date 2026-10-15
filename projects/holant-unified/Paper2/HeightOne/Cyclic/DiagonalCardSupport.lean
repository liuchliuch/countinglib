import Paper2.HeightOne.Cyclic.DiagonalWordGeometry

/-! Cross-edge cards have exactly the merged diagonal cube as support. The
argument counts actual supported words and retains the unique-lift coefficient. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open EndpointSelfLoop
variable {K : Type*} [Field K]

lemma equal_lift_mem_crossCode {n : ℕ} (P : Pairing n) (i j : Fin P.count) (hij : i ≠ j)
    (x : Fin (Fintype.card (crossRemaining P i j)) → Bool) (b : Bool)
    (hx : extendBits (P.ports (i, false)) (P.ports (j, false)) (cross_distinct P i j hij)
      (fun k => x ((Fintype.equivFin (crossRemaining P i j)) k)) b b ∈ equalityCode P) :
    x ∈ crossCode P i j := by
  let a := P.ports (i, false)
  let c := P.ports (j, false)
  let e := Fintype.equivFin (crossRemaining P i j)
  let w := extendBits a c (cross_distinct P i j hij) (fun k => x (e k)) b b
  have hw : w ∈ equalityCode P := hx
  have hword := reconstruct_blockWord P w hw
  apply (mem_crossCode P i j x).mpr
  refine ⟨fun k => w (P.ports (k, false)), ?_, ?_⟩
  · change w a = w c
    simp [w, extendBits, splitPorts, a, c, cross_distinct P i j hij, Ne.symm (cross_distinct P i j hij)]
  · funext k
    change blockWord P (fun k => w (P.ports (k, false))) (e.symm k).val = x k
    rw [hword]
    have he := extendBits_remaining a c (cross_distinct P i j hij) (fun k => x (e k)) b b (e.symm k)
    simpa only [Equiv.apply_symm_apply] using he

/-- Every actual support point of a cross-edge card has a supported lift, and
that lift lies in the original global matching code. -/
theorem cross_card_support_subset {n : ℕ} (f : Signature K n) (P : Pairing n)
    (hF : support f ⊆ equalityCode P) (i j : Fin P.count) (hij : i ≠ j) (s : K) :
    support (Tensor.reindex (Fintype.equivFin (crossRemaining P i j))
      (plusContraction (P.ports (i, false)) (P.ports (j, false)) (cross_distinct P i j hij) s f)) ⊆ crossCode P i j := by
  intro x hx
  rw [mem_support] at hx
  rw [Tensor.reindex_apply, plusContraction_apply] at hx
  by_cases h0 : f (extendBits (P.ports (i, false)) (P.ports (j, false)) (cross_distinct P i j hij)
      (fun k => x ((Fintype.equivFin (crossRemaining P i j)) k)) false false) ≠ 0
  · exact equal_lift_mem_crossCode P i j hij x false (hF ((mem_support _ _).mpr h0))
  · have h1 : f (extendBits (P.ports (i, false)) (P.ports (j, false)) (cross_distinct P i j hij)
        (fun k => x ((Fintype.equivFin (crossRemaining P i j)) k)) true true) ≠ 0 := by
      intro he
      exact hx (by simp [not_ne_iff.mp h0, he])
    exact equal_lift_mem_crossCode P i j hij x true (hF ((mem_support _ _).mpr h1))

/-- Matching cards attain the entire diagonal cube: the inclusion above has
the same cardinality on both sides. -/
theorem cross_card_support_eq {n : ℕ} (f : Signature K n) (P : Pairing n)
    (hF : support f ⊆ equalityCode P) (i j : Fin P.count) (hij : i ≠ j) (s : K)
    (hcard : EqualityMatchingSupport
      (plusContraction (P.ports (i, false)) (P.ports (j, false)) (cross_distinct P i j hij) s f)) :
    support (Tensor.reindex (Fintype.equivFin (crossRemaining P i j))
      (plusContraction (P.ports (i, false)) (P.ports (j, false)) (cross_distinct P i j hij) s f)) = crossCode P i j := by
  obtain ⟨Q, hQ⟩ := hcard
  apply Finset.eq_of_subset_of_card_le (cross_card_support_subset f P hF i j hij s)
  rw [hQ, crossCode_card P i j hij, equalityCode_card]

/-- The exact unique-lift value, including the nonzero unary phase on the
common bit. This remains an analytic identity rather than a gadget assertion. -/
theorem cross_card_value {n : ℕ} (f : Signature K n) (P : Pairing n)
    (hF : support f ⊆ equalityCode P) (i j : Fin P.count) (hij : i ≠ j)
    (s : K) (t : Fin P.count → Bool) (ht : t i = t j) :
    Tensor.reindex (Fintype.equivFin (crossRemaining P i j))
      (plusContraction (P.ports (i, false)) (P.ports (j, false)) (cross_distinct P i j hij) s f)
        (residualBlockWord P i j t) = (if t i then -s else 1) * f (blockWord P t) := by
  let a := P.ports (i, false)
  let b := P.ports (j, false)
  let hab := cross_distinct P i j hij
  have hy : (fun k : crossRemaining P i j => residualBlockWord P i j t
      ((Fintype.equivFin (crossRemaining P i j)) k)) = restrict a b (blockWord P t) := by
    funext k
    simp [residualBlockWord, restrict]
  change plusContraction a b hab s f _ = _
  rw [hy, plusContraction_apply]
  have he : extendBits a b hab (restrict a b (blockWord P t)) (t i) (t i) = blockWord P t := by
    have h := extendBits_restrict a b hab (blockWord P t)
    simpa only [a, b, blockWord, Equiv.symm_apply_apply, ← ht] using h
  have hz : f (extendBits a b hab (restrict a b (blockWord P t)) (!(t i)) (!(t i))) = 0 := by
    by_contra hn
    have hcode := (mem_equalityCode P _).mp (hF ((mem_support _ _).mpr hn)) i
    have hfirst : extendBits a b hab (restrict a b (blockWord P t)) (!(t i)) (!(t i)) a = !(t i) := by
      simp [extendBits, splitPorts]
    have hsecond : extendBits a b hab (restrict a b (blockWord P t)) (!(t i)) (!(t i)) (P.ports (i, true)) = t i := by
      have h := extendBits_remaining a b hab (restrict a b (blockWord P t)) (!(t i)) (!(t i)) (retainedSecond P i j i)
      simpa only [retainedSecond, restrict, blockWord, Equiv.symm_apply_apply] using h
    change _ = _ at hcode
    rw [hfirst, hsecond] at hcode
    exact Bool.not_ne_self (t i) hcode
  cases hti : t i
  · simp only [hti, Bool.not_false] at he hz ⊢
    rw [he, hz]
    simp
  · simp only [hti, Bool.not_true] at he hz ⊢
    rw [he, hz]
    simp

end
end Paper2.HeightOne.Cyclic
