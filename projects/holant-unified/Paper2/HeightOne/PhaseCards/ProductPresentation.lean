import Paper2.HeightOne.PhaseCards.PhaseProduct
import Paper2.Tractable.KPresentation

/-! Every literal phase-block product belongs to the source's standard product
normal form. The fixed Walsh matrix simultaneously transforms the signatures
and the native edge; it is not inserted into a gadget. -/
namespace Paper2.Tractable
noncomputable section
open scoped BigOperators

namespace ProductFactor

def rename {m n : ℕ} (p : Fin m → Fin n) : ProductFactor m → ProductFactor n
  | .unary i u hu => .unary (p i) u hu
  | .equality i j => .equality (p i) (p j)
  | .disequality i j => .disequality (p i) (p j)

lemma eval_rename {m n : ℕ} (p : Fin m → Fin n) (h : ProductFactor m)
    (x : Fin n → Bool) : (h.rename p).eval x = h.eval (x ∘ p) := by
  cases h <;> rfl

end ProductFactor

lemma Product.rename {m n : ℕ} {f : Signature AlgebraicComplex m}
    (hf : Product f) (p : Fin m → Fin n) : Product (fun x => f (x ∘ p)) := by
  rcases hf with rfl | ⟨c, hc, fs, rfl⟩
  · exact product_zero n
  · refine Or.inr ⟨c, hc, fs.map (ProductFactor.rename p), ?_⟩
    funext x
    simp [productFormula, List.map_map, Function.comp_def, ProductFactor.eval_rename]

lemma Product.finset_prod {I : Type*} {n : ℕ} (S : Finset I)
    (f : I → Signature AlgebraicComplex n) (hf : ∀ i ∈ S, Product (f i)) :
    Product (fun x => ∏ i ∈ S, f i x) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using product_constant n 1
  | @insert i S hi ih =>
    have h := (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa [Finset.prod_insert hi] using h

lemma Product.decomposition {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (hf : ∀ i, Product (D.factor i)) : Product D.value := by
  have h := Product.finset_prod Finset.univ
    (fun i x => D.factor i (fun j => x (D.ports ⟨i, j⟩)))
    (fun i _ => (hf i).rename (fun j => D.ports ⟨i, j⟩))
  exact h.scale (D.scale : AlgebraicComplex)

end
end Paper2.Tractable

namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable GroupSplit GroupSplit.MatrixGroup
open scoped BigOperators

lemma star_constraints_iff {n : ℕ} (i : Fin n) (a x : Fin n → Bool) :
    (∀ j, (x i == x j) = (a i == a j)) ↔ x = a ∨ x = fun j => !(a j) := by
  constructor
  · intro h
    by_cases he : x i = a i
    · left
      funext j
      have hj := h j
      rw [he] at hj
      cases ha : a i <;> cases hxa : x j <;> cases haj : a j <;> simp_all
    · right
      funext j
      have hj := h j
      cases hxi : x i <;> cases hai : a i <;>
        cases hxj : x j <;> cases haj : a j <;> simp_all
  · rintro (rfl | rfl)
    · exact fun _ => rfl
    · intro j
      change ((!a i) == (!a j)) = (a i == a j)
      cases a i <;> cases a j <;> rfl

lemma product_star_constraint {n : ℕ} (i j : Fin n) (a : Fin n → Bool) :
    Product (fun x => if (x i == x j) = (a i == a j) then (1 : AlgebraicComplex) else 0) := by
  by_cases h : a i = a j
  · convert product_equality i j using 1
    funext x
    simp [h, Signature.equality]
  · convert product_disequality i j using 1
    funext x
    cases hai : a i <;> cases haj : a j <;>
      cases hxi : x i <;> cases hxj : x j <;> simp_all [Signature.disequality]

/-- A two-point complementary block is a unary weight at one root times an
explicit star of equality/disequality factors. No phase condition is needed. -/
theorem twoPoint_product {n : ℕ} (hn : 0 < n) (a : Fin n → Bool) (r : AlgebraicComplex) :
    Product (twoPoint a r) := by
  classical
  let i : Fin n := ⟨0, hn⟩
  let u : Bool → AlgebraicComplex := fun b => if b = a i then 1 else r
  let edge (j : Fin n) : Signature AlgebraicComplex n := fun x =>
    if (x i == x j) = (a i == a j) then 1 else 0
  have hprod := (product_unary i u).mul
    (Product.finset_prod Finset.univ edge (fun j _ => product_star_constraint i j a))
  have he : (fun x => u (x i) * ∏ j, edge j x) = twoPoint a r := by
    funext x
    have hneq : a ≠ fun j => !(a j) := by
      intro h
      have hi := congrFun h i
      exact Bool.not_ne_self (a i) hi.symm
    have hedge : (∏ j, edge j x) = if x = a ∨ x = (fun j => !(a j)) then 1 else 0 := by
      simp only [edge, Fintype.prod_boole, star_constraints_iff i a x]
    rw [hedge]
    by_cases hxa : x = a
    · subst x
      simp [u, twoPoint, point, hneq]
    · by_cases hxc : x = fun j => !(a j)
      · subst x
        have hai : (!(a i)) ≠ a i := by cases a i <;> decide
        simp [u, twoPoint, point, hxa, hai]
      · simp [u, twoPoint, point, hxa, hxc]
  rw [he] at hprod
  exact hprod

lemma EvenPhaseBlock.product {N n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : EvenPhaseBlock N f) : Product f := by
  obtain ⟨k, a, r, hn, hr, rfl⟩ := hf
  exact twoPoint_product (by omega) a r

/-- The phase-product subclass has the literal standard Product normal form. -/
theorem PhaseProduct.product {N n : ℕ} {f : Signature AlgebraicComplex n}
    (hf : PhaseProduct N f) : Product f := by
  rcases hf with rfl | ⟨m, D, e, hD, rfl⟩
  · exact product_zero n
  · exact (Product.decomposition D (fun i => (hD i).product)).rename e

end
end Paper2.HeightOne.PhaseCards
