import Paper2.MatchingPropagation.Basic
import Paper2.HighHeightNormalization.Attachments

/-! Invertible local diagonal attachments cannot create matching-product
structure. The inverse coefficients below are explicit; port order and the
nonzero global scalar are retained. -/
namespace Paper2.RelativeEO
open scoped BigOperators
open MatchingPropagation
variable {ι : Type} {K : Type*} [Fintype ι] [Field K]

/-- The product over all ports regrouped by the actual oriented matching. -/
theorem pairing_diagonal_product (P : Matching ι) (w : ι → Bool → K) (x : ι → Bool) :
    (∏ i, w i (x i)) = ∏ j, w (P.ports (j,false)) (x (P.ports (j,false))) *
      w (P.ports (j,true)) (x (P.ports (j,true))) := by
  rw [← P.ports.prod_comp (fun i => w i (x i)),Fintype.prod_prod_type]
  simp only [Fintype.prod_bool,mul_comm]

/-- Explicit inverse local weights for both ordered entries of each factor. -/
theorem diagonal_matching_pullback (w : ι → Bool → K) (hw : ∀ i b, w i b ≠ 0)
    (F : Tensor K ι) (h : IsWeighted (fun x => (∏ i, w i (x i)) * F x)) :
    IsWeighted F := by
  classical
  obtain ⟨P,p,q,c,hc,hp,hq,hform⟩ := h
  let a : Fin P.count → K := fun j =>
    p j / (w (P.ports (j,false)) false * w (P.ports (j,true)) true)
  let b : Fin P.count → K := fun j =>
    q j / (w (P.ports (j,false)) true * w (P.ports (j,true)) false)
  have ha : ∀ j, a j ≠ 0 := fun j => div_ne_zero (hp j) (mul_ne_zero (hw _ _) (hw _ _))
  have hb : ∀ j, b j ≠ 0 := fun j => div_ne_zero (hq j) (mul_ne_zero (hw _ _) (hw _ _))
  refine ⟨P,a,b,c,hc,ha,hb,?_⟩
  funext x
  have hd : (∏ i, w i (x i)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hw i (x i))
  apply mul_left_cancel₀ hd
  have hfac (j : Fin P.count) :
      (w (P.ports (j,false)) (x (P.ports (j,false))) *
       w (P.ports (j,true)) (x (P.ports (j,true)))) *
      WeightedMatching.binary (a j) (b j) (x (P.ports (j,false))) (x (P.ports (j,true))) =
      WeightedMatching.binary (p j) (q j) (x (P.ports (j,false))) (x (P.ports (j,true))) := by
    cases h₀ : x (P.ports (j,false)) <;> cases h₁ : x (P.ports (j,true)) <;>
      simp [WeightedMatching.binary,a,b] <;> field_simp [hw] <;> ring
  rw [congrFun hform x,pairing_diagonal_product P]
  unfold product
  rw [mul_left_comm,← Finset.prod_mul_distrib]
  congr 1
  exact Finset.prod_congr rfl (fun j _ => (hfac j).symm)

/-- Several attachments on the same port multiply into one local weight. -/
noncomputable def collectedDiagonal {m : ℕ} (ports : Fin m → ι)
    (v : Fin m → Bool → K) (i : ι) (b : Bool) : K := by
  classical
  exact ∏ j, if ports j = i then v j b else 1

theorem collectedDiagonal_ne_zero {m : ℕ} (ports : Fin m → ι)
    (v : Fin m → Bool → K) (hv : ∀ j b, v j b ≠ 0) (i : ι) (b : Bool) :
    collectedDiagonal ports v i b ≠ 0 := by
  classical
  unfold collectedDiagonal
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  split_ifs
  · exact hv j b
  · exact one_ne_zero

theorem collectedDiagonal_product {m : ℕ} (ports : Fin m → ι)
    (v : Fin m → Bool → K) (x : ι → Bool) :
    (∏ i, collectedDiagonal ports v i (x i)) = ∏ j, v j (x (ports j)) := by
  classical
  unfold collectedDiagonal
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  simp

/-- The complex normalized tensor used by §8 can be pulled back through the
actual finite sequence, even if the same port occurs repeatedly. -/
theorem attachFamily_matching_pullback {m : ℕ} (ports : Fin m → ι) (z : Fin m → ℂ)
    (hz : ∀ j, z j ≠ 0) (F : Tensor ℂ ι)
    (h : IsWeighted (HighHeightNormalization.attachFamily ports z F)) : IsWeighted F := by
  let w := collectedDiagonal ports (fun j => HighHeightNormalization.matingWeight (z j))
  apply diagonal_matching_pullback w
    (collectedDiagonal_ne_zero ports _ (fun j b => HighHeightNormalization.matingWeight_ne_zero (hz j) b)) F
  have he : (fun x => (∏ i, w i (x i)) * F x) =
      HighHeightNormalization.attachFamily ports z F := by
    funext x
    rw [HighHeightNormalization.attachFamily_apply]
    exact congrArg (fun t => t*F x) (collectedDiagonal_product ports _ x)
  exact he ▸ h

end Paper2.RelativeEO
