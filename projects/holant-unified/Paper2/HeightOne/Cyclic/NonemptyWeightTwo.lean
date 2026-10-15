import Paper2.HeightOne.Cyclic.LiftWords
import Paper2.HeightOne.Cyclic.ProductCards
import Paper2.HeightOne.Cyclic.Origin
import Paper2.HeightOne.Dihedral.CubeFactorization

/-! Source cyclic-collapse Step 3. A nonempty matching rectangle gives a
nonzero quadratic coefficient, which cannot vanish at three phases. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable EndpointSelfLoop

def edgeWord {n : ℕ} (P : Pairing n) (i : Fin P.count) : Fin n → Bool :=
  weightTwoWord (P.ports (i, false)) (P.ports (i, true))

lemma edgeWord_mem {n : ℕ} (P : Pairing n) (i : Fin P.count) : edgeWord P i ∈ equalityCode P := by
  apply (weightTwoWord_mem_iff P _ _ (by simp)).mpr
  simp

lemma edgeWords_disjoint {n : ℕ} (P : Pairing n) (i j : Fin P.count) (hij : i ≠ j)
    (k : Fin n) : ¬ (edgeWord P i k = true ∧ edgeWord P j k = true) := by
  simp only [edgeWord, weightTwoWord, decide_eq_true_eq]
  rintro ⟨hi | hi, hj | hj⟩ <;> have h := P.ports.injective (hi.symm.trans hj) <;>
    exact hij (congrArg Prod.fst h)

lemma edgeWords_rectangle {n : ℕ} (P : Pairing n) (i j : Fin P.count) (hij : i ≠ j) :
    PortRectangle (fun _ => false) (xorWord (edgeWord P i) (edgeWord P j))
      (edgeWord P i) (edgeWord P j) := by
  intro k
  have h := edgeWords_disjoint P i j hij k
  cases hi : edgeWord P i k <;> cases hj : edgeWord P j k <;>
    simp_all [xorWord]

/-- A pencil of nonzero Product tensors with one fixed matching support
cannot have all its constant-slice weight-two coefficients zero. -/
theorem no_matching_product_pencil_without_edges {n : ℕ} (hn : 4 ≤ n)
    (A B : Signature AlgebraicComplex n) (S : Set AlgebraicComplex)
    (hthree : ∃ s ∈ S, ∃ t ∈ S, ∃ u ∈ S, s ≠ t ∧ s ≠ u ∧ t ≠ u)
    (P : Pairing n) (hP : ∀ s ∈ S, support (pencil A B s) = equalityCode P)
    (hprod : ∀ s ∈ S, Product (pencil A B s))
    (hA0 : A (fun _ => false) ≠ 0) (hB0 : B (fun _ => false) = 0)
    (hA : ∀ p q, p ≠ q → A (weightTwoWord p q) = 0) : False := by
  have hcount := Matching.pair_count P
  let i : Fin P.count := ⟨0, by omega⟩
  let j : Fin P.count := ⟨1, by omega⟩
  have hij : i ≠ j := by intro he; have := congrArg Fin.val he; simp [i, j] at this
  let x := edgeWord P i
  let y := edgeWord P j
  let z := xorWord x y
  have hx : x ∈ equalityCode P := edgeWord_mem P i
  have hy : y ∈ equalityCode P := edgeWord_mem P j
  have hz : z ∈ equalityCode P := equalityCode_xorClosed P x hx y hy
  have h0 : (fun _ => false) ∈ equalityCode P := (mem_equalityCode _ _).mpr (fun _ => rfl)
  have hAx : A x = 0 := hA _ _ (by simp)
  have hAy : A y = 0 := hA _ _ (by simp)
  have hnonzero (s) (hs : s ∈ S) (w) (hw : w ∈ equalityCode P) : pencil A B s w ≠ 0 := by
    rw [← hP s hs, mem_support] at hw
    exact hw
  obtain ⟨s, hs, t, ht, u, hu, hst, hsu, htu⟩ := hthree
  have hBx : B x ≠ 0 := by
    intro he
    exact hnonzero s hs x hx (by simp [pencil, hAx, he])
  have hBy : B y ≠ 0 := by
    intro he
    exact hnonzero s hs y hy (by simp [pencil, hAy, he])
  have hpoly (q) (hq : q ∈ S) : A (fun _ => false) * A z +
      (-(A (fun _ => false) * B z)) * q + (-(B x * B y)) * q ^ 2 = 0 := by
    have h := (hprod q hq).rectangle (fun _ => false) z x y
      (hnonzero q hq _ h0) (hnonzero q hq _ hz) (hnonzero q hq _ hx) (hnonzero q hq _ hy)
      (edgeWords_rectangle P i j hij)
    simp only [pencil, hB0, hAx, hAy, mul_zero, sub_zero, zero_sub] at h
    linear_combination h
  have hc := (Dihedral.quadratic_three_roots _ _ _ s t u hst hsu htu
    (hpoly s hs) (hpoly t ht) (hpoly u hu)).2.2
  exact (neg_ne_zero.mpr (mul_ne_zero hBx hBy)) hc

/-- Above four ports, a tensor all of whose phase cards have matching Product
form has at least one nonzero weight-two coefficient. -/
theorem exists_weightTwo_of_matching_product_cards {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : f ≠ 0) (hn : 6 ≤ n) (S : Set AlgebraicComplex)
    (hthree : ∃ s ∈ S, ∃ t ∈ S, ∃ u ∈ S, s ≠ t ∧ s ≠ u ∧ t ≠ u)
    (hcards : ∀ a b (hab : a ≠ b), ∀ q ∈ S, plusContraction a b hab q f ≠ 0 →
      EqualityMatchingSupport (plusContraction a b hab q f))
    (hprod : ∀ a b (hab : a ≠ b), ∀ q ∈ S,
      Product (Tensor.reindex (Fintype.equivFin (Remaining a b)) (plusContraction a b hab q f))) :
    ∃ u v, u ≠ v ∧ f (pairWord u v) ≠ 0 := by
  classical
  by_contra hW
  push Not at hW
  have h0 := origin_nonzero_of_matching_cards f hf (by omega) S hthree hcards
  let a : Fin n := ⟨0, by omega⟩
  let b : Fin n := ⟨1, by omega⟩
  have hab : a ≠ b := by intro h; have := congrArg Fin.val h; simp [a, b] at this
  let e := Fintype.equivFin (Remaining a b)
  let A := Tensor.reindex e (fun x => f (extendBits a b hab x false false))
  let B := Tensor.reindex e (fun x => f (extendBits a b hab x true true))
  have hpencil (s : AlgebraicComplex) : pencil A B s = Tensor.reindex e (plusContraction a b hab s f) := by
    funext x
    simp only [A, B, pencil, Tensor.reindex_apply, plusContraction_apply]
  have hA0 : A (fun _ => false) ≠ 0 := by
    simpa only [A, Tensor.reindex_apply, extendBits_origin_false] using h0
  have hB0 : B (fun _ => false) = 0 := by
    simpa only [B, Tensor.reindex_apply, extendBits_origin_true] using hW a b hab
  have hnz (s : AlgebraicComplex) : pencil A B s ≠ 0 := by
    intro hz
    apply hA0
    have he := congrFun hz (fun _ => false)
    simpa only [pencil, hB0, mul_zero, sub_zero, Pi.zero_apply] using he
  have hm : ∀ s ∈ S, pencil A B s ≠ 0 → ∃ P : Pairing (Fintype.card (Remaining a b)),
      support (pencil A B s) = equalityCode P := by
    intro s hs hsn
    rw [hpencil] at hsn ⊢
    exact hcards a b hab s hs (fun hz => hsn ((reindex_eq_zero_iff e _).mpr hz))
  rcases phase_independent_matching A B S hthree hm with hzero | ⟨P, hP, _⟩
  · exact hA0 (congrFun hzero.1 _)
  · apply no_matching_product_pencil_without_edges (by have h := remaining_card a b hab; simp only [Fintype.card_fin] at h; omega)
      A B S hthree P (fun s hs => hP s hs (hnz s))
      (fun s hs => by rw [hpencil]; exact hprod a b hab s hs) hA0 hB0
    intro p q hpq
    exact zero_slice_weightTwo f hW a b hab p q hpq

end
end Paper2.HeightOne.Cyclic
