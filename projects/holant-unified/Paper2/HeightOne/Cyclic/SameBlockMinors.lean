import Paper2.HeightOne.Cyclic.SameBlockGeometry
import Paper2.HeightOne.PhaseCards.ProductRectangles
import Paper2.HeightOne.Dihedral.CubeFactorization

/-! Three phases of a same-block card force the endpoint logical face minors
of the original tensor to vanish. Zero cards are handled literally. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable EndpointSelfLoop

lemma same_extend_update {n : ℕ} (P : Pairing n) (i : Fin P.count)
    (t : Fin P.count → Bool) (b : Bool) :
    extendBits (P.ports (i, false)) (P.ports (i, true)) (same_distinct P i)
      (restrict (P.ports (i, false)) (P.ports (i, true)) (blockWord P t)) b b =
      blockWord P (Function.update t i b) := by
  classical
  funext k
  obtain ⟨⟨j, c⟩, rfl⟩ := P.ports.surjective k
  by_cases hj : j = i
  · subst j
    cases c <;> simp [extendBits, splitPorts, blockWord]
  · have hr : P.ports (j, c) ≠ P.ports (i, false) ∧ P.ports (j, c) ≠ P.ports (i, true) := by simp [hj]
    have h := extendBits_remaining (P.ports (i, false)) (P.ports (i, true)) (same_distinct P i)
      (restrict (P.ports (i, false)) (P.ports (i, true)) (blockWord P t)) b b ⟨P.ports (j, c), hr⟩
    simpa only [restrict, blockWord, Equiv.symm_apply_apply, Function.update_of_ne hj] using h

lemma same_card_value {K : Type*} [Field K] {n : ℕ} (f : Signature K n) (P : Pairing n)
    (i : Fin P.count) (s : K) (t : Fin P.count → Bool) :
    Tensor.reindex (Fintype.equivFin (sameRemaining P i))
      (plusContraction (P.ports (i, false)) (P.ports (i, true)) (same_distinct P i) s f)
        (sameResidualWord P i t) =
      f (blockWord P (Function.update t i false)) - s * f (blockWord P (Function.update t i true)) := by
  rw [Tensor.reindex_apply, plusContraction_apply]
  have hy : (fun k : sameRemaining P i => sameResidualWord P i t
      ((Fintype.equivFin (sameRemaining P i)) k)) =
      restrict (P.ports (i, false)) (P.ports (i, true)) (blockWord P t) := by
    funext k
    simp only [sameResidualWord, Equiv.symm_apply_apply, restrict]
  rw [hy, same_extend_update, same_extend_update]

/-- The logical rectangle identity of every same-block pencil member,
including a member that vanishes identically. -/
theorem same_card_rectangle {n : ℕ} (f : Signature AlgebraicComplex n) (P : Pairing n)
    (hF : support f ⊆ equalityCode P) (i : Fin P.count) (s : AlgebraicComplex)
    (hmatch : plusContraction (P.ports (i, false)) (P.ports (i, true)) (same_distinct P i) s f ≠ 0 →
      EqualityMatchingSupport (plusContraction (P.ports (i, false)) (P.ports (i, true)) (same_distinct P i) s f))
    (hprod : Product (Tensor.reindex (Fintype.equivFin (sameRemaining P i))
      (plusContraction (P.ports (i, false)) (P.ports (i, true)) (same_distinct P i) s f)))
    (x y z w : Fin P.count → Bool) (hr : PortRectangle x y z w) :
    let q := fun t => f (blockWord P (Function.update t i false)) - s * f (blockWord P (Function.update t i true))
    q x * q y = q z * q w := by
  let c := plusContraction (P.ports (i, false)) (P.ports (i, true)) (same_distinct P i) s f
  let q := Tensor.reindex (Fintype.equivFin (sameRemaining P i)) c
  change (f _ - s * f _) * (f _ - s * f _) = (f _ - s * f _) * (f _ - s * f _)
  simp only [← same_card_value f P i s]
  change q (sameResidualWord P i x) * q (sameResidualWord P i y) =
    q (sameResidualWord P i z) * q (sameResidualWord P i w)
  by_cases hc : c = 0
  · simp only [q, hc, Tensor.reindex_apply, Pi.zero_apply, mul_zero]
  · have he := same_card_support_eq f P hF i s (hmatch hc)
    have hn (t) : q (sameResidualWord P i t) ≠ 0 := by
      have hm := sameResidualWord_mem P i t
      rw [← he, mem_support] at hm
      exact hm
    exact hprod.rectangle _ _ _ _ (hn x) (hn y) (hn z) (hn w)
      (fun k => hr (P.ports.symm ((Fintype.equivFin (sameRemaining P i)).symm k).val).1)

/-- At either endpoint of a same-block pencil every logical rectangle has
zero determinant. These are actual coefficient equations of f. -/
theorem same_block_endpoint_rectangles {n : ℕ} (f : Signature AlgebraicComplex n) (P : Pairing n)
    (hF : support f ⊆ equalityCode P) (i : Fin P.count)
    (s t u : AlgebraicComplex) (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hmatch : ∀ q, q = s ∨ q = t ∨ q = u →
      plusContraction (P.ports (i, false)) (P.ports (i, true)) (same_distinct P i) q f ≠ 0 →
      EqualityMatchingSupport (plusContraction (P.ports (i, false)) (P.ports (i, true)) (same_distinct P i) q f))
    (hprod : ∀ q, q = s ∨ q = t ∨ q = u → Product (Tensor.reindex (Fintype.equivFin (sameRemaining P i))
      (plusContraction (P.ports (i, false)) (P.ports (i, true)) (same_distinct P i) q f)))
    (x y z w : Fin P.count → Bool) (hr : PortRectangle x y z w) (b : Bool) :
    f (blockWord P (Function.update x i b)) * f (blockWord P (Function.update y i b)) =
      f (blockWord P (Function.update z i b)) * f (blockWord P (Function.update w i b)) := by
  let A : Bool → Bool → AlgebraicComplex := fun a b =>
    f (blockWord P (Function.update (if a then (if b then y else w) else (if b then z else x)) i false))
  let B : Bool → Bool → AlgebraicComplex := fun a b =>
    f (blockWord P (Function.update (if a then (if b then y else w) else (if b then z else x)) i true))
  have hdet (q) (hq : q = s ∨ q = t ∨ q = u) : Dihedral.detTwo (fun a b => A a b - q * B a b) = 0 := by
    have h := same_card_rectangle f P hF i q (hmatch q hq) (hprod q hq) x y z w hr
    exact sub_eq_zero.mpr h
  have h := Dihedral.pencil_det_endpoint_faces A B s t u hst hsu htu
    (hdet s (Or.inl rfl)) (hdet t (Or.inr (Or.inl rfl))) (hdet u (Or.inr (Or.inr rfl)))
  cases b
  · exact sub_eq_zero.mp h.1
  · exact sub_eq_zero.mp h.2

end
end Paper2.HeightOne.Cyclic
