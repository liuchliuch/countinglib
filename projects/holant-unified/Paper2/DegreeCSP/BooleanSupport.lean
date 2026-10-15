import Paper2.DegreeCSP.BooleanStructure
import Paper2.Paper1ProvedCriteria
import Holant.ReedMuller.AffinePatching.ReconstructionSupport

/-! Actual product and affine support indicators for the two Boolean
Mal'tsev cases. This does not replace coefficient/phase classification. -/
namespace Paper2.DegreeCSP.BooleanStructure
open Tractable
noncomputable section
attribute [local instance] Classical.propDecidable

def indicator {n : ℕ} (R : Set (Fin n → Bool)) : Signature AlgebraicComplex n :=
  fun x => if x ∈ R then 1 else 0

@[simp] theorem indicator_ne_zero {n : ℕ} (R : Set (Fin n → Bool)) (x : Fin n → Bool) :
    indicator R x ≠ 0 ↔ x ∈ R := by
  classical
  by_cases hx : x ∈ R <;> simp [indicator,hx]

/-- The xor case supplies an actual finite affine-system indicator. -/
theorem affine_indicator_of_xor {n : ℕ} (R : Set (Fin n → Bool))
    (hR : Preserves xor3 R) : Affine (indicator R) := by
  classical
  by_cases hne : R.Nonempty
  · obtain ⟨a,ha⟩ := hne
    have ht : ∀ x y z : Fin n → Bool, indicator R x ≠ 0 → indicator R y ≠ 0 →
        indicator R z ≠ 0 → indicator R
          (Holant.Tractable.AffinePhase.xor (Holant.Tractable.AffinePhase.xor x y) z) ≠ 0 := by
      intro x y z hx hy hz
      apply (indicator_ne_zero _ _).mpr
      exact hR x ((indicator_ne_zero _ _).mp hx) y ((indicator_ne_zero _ _).mp hy)
        z ((indicator_ne_zero _ _).mp hz)
    obtain ⟨S,p,hp,hpn,hpf,hS⟩ := Holant.ReedMuller.AffinePatching.exists_support_retraction
      (indicator R) a ((indicator_ne_zero _ _).mpr ha) ht
    let T : AffineSystem n := (Paper1Proved.affineSystemIso n).symm S
    have hT : ∀ x, T.Holds x ↔ x ∈ R := fun x => (hS x).trans (indicator_ne_zero R x)
    convert affine_indicator T using 1
    funext x
    simp only [indicator,hT]
  · have hz : indicator R = 0 := by
      funext x
      simp [indicator,show x ∉ R from fun hx => hne ⟨x,hx⟩]
    rw [hz]
    exact affine_zero n

def PreservesBinary (m : Operation) (B : Bool → Bool → Prop) : Prop :=
  ∀ a b c d e f, B a b → B c d → B e f → B (m (a,c,e)) (m (b,d,f))

/-- A Boolean binary support preserved by discriminator has only unary,
equality, disequality, or empty/full constraints. -/
theorem binary_indicator_product {n : ℕ} (B : Bool → Bool → Prop)
    (hB : PreservesBinary discriminator B) (i j : Fin n) :
    Product (fun x => if B (x i) (x j) then (1 : AlgebraicComplex) else 0) := by
  classical
  by_cases h00 : B false false <;> by_cases h01 : B false true <;>
    by_cases h10 : B true false <;> by_cases h11 : B true true
  all_goals solve
    | (exfalso; simp_all [PreservesBinary,discriminator,Bool.forall_bool])
    | (convert product_constant n (1 : AlgebraicComplex) using 1
       funext x; cases hi : x i <;> cases hj : x j <;> simp_all)
    | (convert product_constant n (0 : AlgebraicComplex) using 1
       funext x; cases hi : x i <;> cases hj : x j <;> simp_all)
    | (convert product_unary i (fun b => if b = false then 1 else 0) using 1
       funext x; cases hi : x i <;> cases hj : x j <;> simp_all)
    | (convert product_unary i (fun b => if b = true then 1 else 0) using 1
       funext x; cases hi : x i <;> cases hj : x j <;> simp_all)
    | (convert product_unary j (fun b => if b = false then 1 else 0) using 1
       funext x; cases hi : x i <;> cases hj : x j <;> simp_all)
    | (convert product_unary j (fun b => if b = true then 1 else 0) using 1
       funext x; cases hi : x i <;> cases hj : x j <;> simp_all)
    | (convert (product_unary i (fun b => if b = false then 1 else 0)).mul
         (product_unary j (fun b => if b = false then 1 else 0)) using 1
       funext x; cases hi : x i <;> cases hj : x j <;> simp_all)
    | (convert (product_unary i (fun b => if b = false then 1 else 0)).mul
         (product_unary j (fun b => if b = true then 1 else 0)) using 1
       funext x; cases hi : x i <;> cases hj : x j <;> simp_all)
    | (convert (product_unary i (fun b => if b = true then 1 else 0)).mul
         (product_unary j (fun b => if b = false then 1 else 0)) using 1
       funext x; cases hi : x i <;> cases hj : x j <;> simp_all)
    | (convert (product_unary i (fun b => if b = true then 1 else 0)).mul
         (product_unary j (fun b => if b = true then 1 else 0)) using 1
       funext x; cases hi : x i <;> cases hj : x j <;> simp_all)
    | (convert product_equality i j using 1
       funext x; cases hi : x i <;> cases hj : x j <;> simp_all [Signature.equality])
    | (convert product_disequality i j using 1
       funext x; cases hi : x i <;> cases hj : x j <;> simp_all [Signature.disequality])

/-- The actual binary projection retains its support-row witness. -/
def projection {n : ℕ} (R : Set (Fin n → Bool)) (i j : Fin n) (a b : Bool) : Prop :=
  ∃ z ∈ R, z i = a ∧ z j = b

theorem projection_preserves {n : ℕ} (m : Operation) (R : Set (Fin n → Bool))
    (hR : Preserves m R) (i j : Fin n) : PreservesBinary m (projection R i j) := by
  rintro a b c d e f ⟨u,hu,hui,huj⟩ ⟨v,hv,hvi,hvj⟩ ⟨w,hw,hwi,hwj⟩
  refine ⟨fun k => m (u k,v k,w k),hR u hu v hv w hw,?_,?_⟩
  · simp only [hui,hvi,hwi]
  · simp only [huj,hvj,hwj]

theorem product_finset {n : ℕ} {ι : Type} (s : Finset ι)
    (F : ι → Signature AlgebraicComplex n) (h : ∀ i ∈ s, Product (F i)) :
    Product (fun x => ∏ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using product_constant n (1 : AlgebraicComplex)
  | @insert i s hi ih =>
    have hprod := (h i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))
    simpa only [Finset.prod_insert hi] using hprod

/-- The discriminator case reconstructs an actual product-class support
indicator, including repeated coordinates and the empty relation. -/
theorem product_indicator_of_discriminator {n : ℕ} (R : Set (Fin n → Bool))
    (hR : Preserves discriminator R) : Product (indicator R) := by
  classical
  by_cases hne : R.Nonempty
  · let F : (Fin n × Fin n) → Signature AlgebraicComplex n := fun p x =>
      if projection R p.1 p.2 (x p.1) (x p.2) then 1 else 0
    have hf : ∀ p ∈ (Finset.univ : Finset (Fin n × Fin n)), Product (F p) := by
      intro p _
      exact binary_indicator_product _ (projection_preserves discriminator R hR p.1 p.2) p.1 p.2
    have hp := product_finset Finset.univ F hf
    convert hp using 1
    funext x
    by_cases hx : x ∈ R
    · simp only [indicator,ite_eq_left hx]
      symm
      apply Finset.prod_eq_one
      intro p _
      exact ite_eq_left ⟨x,hx,rfl,rfl⟩
    · have hbad : ∃ i j, ¬ projection R i j (x i) (x j) := by
        by_contra hn
        apply hx
        apply pairwise_reconstruct R hne (preserves_majority hR) x
        have hall : ∀ i j, projection R i j (x i) (x j) := by
          simpa only [not_exists,not_not] using hn
        exact hall
      obtain ⟨i,j,hij⟩ := hbad
      simp only [indicator,ite_eq_right hx]
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ (i,j))
      exact ite_eq_right hij
  · have hz : indicator R = 0 := by
      funext x
      simp [indicator,show x ∉ R from fun hx => hne ⟨x,hx⟩]
    rw [hz]
    exact product_zero n

end
end Paper2.DegreeCSP.BooleanStructure
