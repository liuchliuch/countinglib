import Paper2.HeightOne.Cyclic.DiagonalCardSupport
import Paper2.HeightOne.PhaseCards.ProductDiagonals

/-! The logical coefficient table on the proved global matching has full
support and literal unary-product equal-coordinate slices. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable EndpointSelfLoop

lemma cross_pairWord_not_mem {n : ℕ} (P : Pairing n) (i j : Fin P.count) (hij : i ≠ j) :
    pairWord (P.ports (i, false)) (P.ports (j, false)) ∉ equalityCode P := by
  intro h
  have he := (mem_equalityCode P _).mp h i
  simp [pairWord] at he

lemma cross_card_origin {K : Type*} [Field K] {n : ℕ} (f : Signature K n) (P : Pairing n)
    (hF : support f ⊆ equalityCode P) (i j : Fin P.count) (hij : i ≠ j) (s : K) :
    plusContraction (P.ports (i, false)) (P.ports (j, false)) (cross_distinct P i j hij) s f
      (fun _ => false) = f (fun _ => false) := by
  rw [plusContraction_apply, extendBits_origin_false, extendBits_origin_true]
  have hz : f (pairWord (P.ports (i, false)) (P.ports (j, false))) = 0 := by
    by_contra he
    exact cross_pairWord_not_mem P i j hij (hF ((mem_support _ _).mpr he))
  rw [hz, mul_zero, sub_zero]

/-- One nonzero phase is enough to expose every logical assignment through a
cross-edge card, because three logical bits always contain an equal pair. -/
theorem logical_full_support {K : Type*} [Field K] {n : ℕ} (f : Signature K n) (P : Pairing n)
    (hP : 3 ≤ P.count) (hF : support f ⊆ equalityCode P) (h0 : f (fun _ => false) ≠ 0)
    (s : K)
    (hcards : ∀ a b (hab : a ≠ b), plusContraction a b hab s f ≠ 0 →
      EqualityMatchingSupport (plusContraction a b hab s f)) :
    ∀ t, f (blockWord P t) ≠ 0 := by
  intro t
  obtain ⟨i, j, hij, ht⟩ := Fintype.exists_ne_map_eq_of_card_lt t (by simp only [Fintype.card_fin, Fintype.card_bool]; omega)
  have hcn : plusContraction (P.ports (i, false)) (P.ports (j, false)) (cross_distinct P i j hij) s f ≠ 0 := by
    intro he
    have hz := congrFun he (fun _ => false)
    rw [cross_card_origin f P hF i j hij s] at hz
    exact h0 hz
  have heq := cross_card_support_eq f P hF i j hij s (hcards _ _ _ hcn)
  have hm : residualBlockWord P i j t ∈ crossCode P i j := (mem_crossCode _ _ _ _).mpr ⟨t, ht, rfl⟩
  rw [← heq, mem_support, cross_card_value f P hF i j hij s t ht] at hm
  exact (mul_ne_zero_iff.mp hm).2

/-- Correcting the known common-bit phase gives a literal Product table that
agrees with the logical table on the selected diagonal. -/
theorem logical_diagonal_product {n : ℕ} (f : Signature AlgebraicComplex n) (P : Pairing n)
    (hF : support f ⊆ equalityCode P) (s : AlgebraicComplex) (hs : s ≠ 0)
    (i j : Fin P.count) (hij : i ≠ j)
    (hprod : Product (Tensor.reindex (Fintype.equivFin (crossRemaining P i j))
      (plusContraction (P.ports (i, false)) (P.ports (j, false)) (cross_distinct P i j hij) s f))) :
    ∃ g : Signature AlgebraicComplex P.count, Product g ∧
      ∀ t, t i = t j → g t = f (blockWord P t) := by
  let E := Fintype.equivFin (crossRemaining P i j)
  let q := Tensor.reindex E
    (plusContraction (P.ports (i, false)) (P.ports (j, false)) (cross_distinct P i j hij) s f)
  let m : Fin (Fintype.card (crossRemaining P i j)) → Fin P.count :=
    fun k => (P.ports.symm (E.symm k).val).1
  let u : Bool → AlgebraicComplex := fun b => if b then (-s)⁻¹ else 1
  let g : Signature AlgebraicComplex P.count := fun t => u (t i) * q (residualBlockWord P i j t)
  have hg : Product g := (product_unary i u).mul (hprod.rename m)
  refine ⟨g, hg, ?_⟩
  intro t ht
  change u (t i) * q (residualBlockWord P i j t) = _
  rw [show q (residualBlockWord P i j t) = (if t i then -s else 1) * f (blockWord P t) from
    cross_card_value f P hF i j hij s t ht]
  cases t i <;> simp [u, hs, neg_ne_zero.mpr hs, ← mul_assoc]

/-- The exact hypothesis of official Paper 1 Lemma 7.8 is now discharged by
actual contraction Product forms; no logical slice is treated as a gadget. -/
theorem logical_unary_diagonals {n : ℕ} (f : Signature AlgebraicComplex n) (P : Pairing n)
    (hP : 3 ≤ P.count) (hF : support f ⊆ equalityCode P) (h0 : f (fun _ => false) ≠ 0)
    (s : AlgebraicComplex) (hs : s ≠ 0)
    (hcards : ∀ a b (hab : a ≠ b), plusContraction a b hab s f ≠ 0 →
      EqualityMatchingSupport (plusContraction a b hab s f))
    (hprod : ∀ a b (hab : a ≠ b), Product
      (Tensor.reindex (Fintype.equivFin (Remaining a b)) (plusContraction a b hab s f))) :
    DiagonalSlices.UnaryDiagonals (fun t => f (blockWord P t)) := by
  have hfull := logical_full_support f P hP hF h0 s hcards
  intro i j hij
  obtain ⟨g, hg, he⟩ := logical_diagonal_product f P hF s hs i j hij (hprod _ _ _)
  obtain ⟨c, u, hc, hu, hg⟩ := hg.unaryOnDiagonal i j (fun t ht => by rw [he t ht]; exact hfull t)
  exact ⟨c, u, hc, hu, fun t ht => (he t ht).symm.trans (hg t ht)⟩

end
end Paper2.HeightOne.Cyclic
