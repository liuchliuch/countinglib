import Paper2.HeightOne.Dihedral.SixPortOrigin
import Paper2.HeightOne.Cyclic.Factorization

/-! Coefficient reconstruction of the signed six-port base case. An analytic
xor change of indices is distributed through the actual finite decomposition;
the original scalar, factors, and ordered external ports are retained. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Dihedral
noncomputable section
open Cyclic Tractable EndpointSelfLoop

def xorShift {K : Type*} {ι : Type} (a : ι → Bool) (f : (ι → Bool) → K) :=
  fun x => f (xorWord a x)

lemma xorShift_involutive {K : Type*} {ι : Type} (a : ι → Bool) (f : (ι → Bool) → K) :
    xorShift a (xorShift a f) = f := by
  funext x
  change f (xorWord a (xorWord a x)) = f x
  congr 1
  funext i
  simp only [xorWord]
  cases a i <;> cases x i <;> rfl

lemma xorShift_origin {K : Type*} {ι : Type} (a : ι → Bool) (f : (ι → Bool) → K) :
    xorShift a f (fun _ => false) = f a := by
  change f (xorWord a (fun _ => false)) = f a
  congr 1
  funext i
  simp [xorWord]

def shiftedDecomposition {K : Type*} [CommSemiring K] {n : ℕ}
    (D : TensorDecomposition K n) (a : Fin n → Bool) : TensorDecomposition K n where
  count := D.count
  arity := D.arity
  factor i := xorShift (fun j => a (D.ports ⟨i,j⟩)) (D.factor i)
  ports := D.ports
  scale := D.scale

lemma shiftedDecomposition_value {K : Type*} [CommSemiring K] {n : ℕ}
    (D : TensorDecomposition K n) (a : Fin n → Bool) :
    (shiftedDecomposition D a).value = xorShift a D.value := rfl

/-- The support matching and the three-phase minors reconstruct all 64
original coefficients, not merely the eight supported logical entries. -/
theorem six_binary_decomposition_of_origin_cards (f : Signature AlgebraicComplex 6)
    (h0 : f (fun _ => false) ≠ 0) (s t u : AlgebraicComplex)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hmatching : ∀ a b (hab : a ≠ b), ∀ q, q = s ∨ q = t ∨ q = u →
      plusContraction a b hab q f ≠ 0 → EqualityMatchingSupport (plusContraction a b hab q f))
    (hproduct : ∀ a b (hab : a ≠ b), ∀ q, q = s ∨ q = t ∨ q = u →
      Product (Tensor.reindex (Fintype.equivFin (Remaining a b)) (plusContraction a b hab q f))) :
    ∃ D : TensorDecomposition AlgebraicComplex 6, D.value = f ∧ ∀ i, D.arity i = 2 := by
  have hf : f ≠ 0 := by intro h; exact h0 (congrFun h (fun _ => false))
  let S : Set AlgebraicComplex := {q | q = s ∨ q = t ∨ q = u}
  have hthree : ∃ x ∈ S, ∃ y ∈ S, ∃ z ∈ S, x ≠ y ∧ x ≠ z ∧ y ≠ z :=
    ⟨s,Or.inl rfl,t,Or.inr (Or.inl rfl),u,Or.inr (Or.inr rfl),hst,hsu,htu⟩
  obtain ⟨P,_,hP⟩ := matching_core_of_cards f hf (by decide) S hthree hmatching hproduct
  have hcount : P.count = 3 := by have h := Matching.pair_count P; omega
  obtain ⟨ρ,_,hρ⟩ := logical_three_factorization f P hcount hP h0 s t u hst hsu htu
    hmatching hproduct
  exact ⟨equalityDecomposition P (f (fun _ => false)) h0 ρ,
    decomposition_of_logical_product f P hP h0 ρ hρ,fun _ => rfl⟩

/-- A nonzero supported base word may be moved to the origin analytically.
After reconstruction, the inverse index shift gives three ordered binary
factors of the original tensor, without any gadget realization assumption for
the index shift itself. -/
theorem six_binary_decomposition_of_shifted_cards (f : Signature AlgebraicComplex 6)
    (a : Fin 6 → Bool) (ha : f a ≠ 0) (s t u : AlgebraicComplex)
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u)
    (hmatching : ∀ i j (hij : i ≠ j), ∀ q, q = s ∨ q = t ∨ q = u →
      plusContraction i j hij q (xorShift a f) ≠ 0 →
        EqualityMatchingSupport (plusContraction i j hij q (xorShift a f)))
    (hproduct : ∀ i j (hij : i ≠ j), ∀ q, q = s ∨ q = t ∨ q = u →
      Product (Tensor.reindex (Fintype.equivFin (Remaining i j))
        (plusContraction i j hij q (xorShift a f)))) :
    ∃ D : TensorDecomposition AlgebraicComplex 6, D.value = f ∧ ∀ i, D.arity i = 2 := by
  obtain ⟨D,hD,htwo⟩ := six_binary_decomposition_of_origin_cards (xorShift a f)
    (by rwa [xorShift_origin]) s t u hst hsu htu hmatching hproduct
  refine ⟨shiftedDecomposition D a,?_,htwo⟩
  rw [shiftedDecomposition_value,hD,xorShift_involutive]

end
end Paper2.HeightOne.Dihedral

