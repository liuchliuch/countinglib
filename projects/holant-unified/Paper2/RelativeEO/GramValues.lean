import Paper2.RelativeEO.GramNetwork
import Mathlib.Logic.Equiv.Bool

/-! Exact ARS turns the explicitly bilinear two-copy graph into a positive
Gram table. All six central coefficients and its vanishing off the central
layer are proved from the original ordered input, without assuming that an
ambient language has ARS. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
noncomputable section
open Paper2.Tractable Paper2.ExactInput EndpointSelfLoop
open scoped BigOperators
variable {n : ℕ}
local instance (i j : Fin n) : DecidableEq (Remaining i j) := Classical.decEq _

/-- The two exposed bits are the only omitted coordinates. -/
theorem remaining_card (i j : Fin n) (hij : i ≠ j) :
    Fintype.card (Remaining i j) + 2 = n := by
  have h := Fintype.card_congr (splitPorts i j hij)
  simpa only [Fintype.card_sum,Fintype.card_bool,Fintype.card_fin] using h.symm

theorem fillPair_weight (i j : Fin n) (hij : i ≠ j) (a b : Bool)
    (z : Remaining i j → Bool) :
    weight (fillPair i j hij a b z) = weight z + a.toNat + b.toNat := by
  classical
  unfold weight
  rw [← (splitPorts i j hij).symm.sum_comp,Fintype.sum_sum_type]
  have hh (t : Bool) : (if t then (1 : ℕ) else 0) = t.toNat := by cases t <;> rfl
  simp only [fillPair,Equiv.apply_symm_apply,Sum.elim_inl,Sum.elim_inr,Fintype.sum_bool]
  cases a <;> cases b <;> simp [Bool.toNat,add_assoc,add_comm,add_left_comm] <;> omega

/-- Algebraic coercion commutes with the actual native-X sum. -/
theorem gramTable_coe (i j : Fin n) (hij : i ≠ j) (f : Signature AlgebraicComplex n)
    (x : Fin 4 → Bool) :
    (gramTable (K := AlgebraicComplex) i j hij f x : ℂ) = gramTable i j hij (fun y => (f y : ℂ)) x := by
  let φ : AlgebraicComplex →+* ℂ := (algebraicClosure ℚ ℂ).val.toRingHom
  change φ (∑ z, pairSlice (K := AlgebraicComplex) i j hij f (x 0) (x 1) z *
    pairSlice (K := AlgebraicComplex) i j hij f (x 2) (x 3) (fun k => !(z k))) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro z _
  exact map_mul φ _ _

/-- The graph remains EO, independently of ARS. -/
theorem gramTable_central (i j : Fin n) (hij : i ≠ j) (f : Signature AlgebraicComplex n)
    (he : Signature.CentralSupport f) : Signature.CentralSupport (gramTable (K := AlgebraicComplex) i j hij f) := by
  classical
  intro x hx
  unfold gramTable
  apply Finset.sum_eq_zero
  intro z _
  by_contra hn
  obtain ⟨h₁,h₂⟩ := mul_ne_zero_iff.mp hn
  have hw₁ : 2 * weight (fillPair i j hij (x 0) (x 1) z) = n := by
    by_contra hh
    exact h₁ (he _ hh)
  have hw₂ : 2 * weight (fillPair i j hij (x 2) (x 3) (fun k => !(z k))) = n := by
    by_contra hh
    exact h₂ (he _ hh)
  rw [fillPair_weight] at hw₁ hw₂
  have hc := weight_complement_add z
  have hn := remaining_card i j hij
  have hquad : weight x = (x 0).toNat + (x 1).toNat + (x 2).toNat + (x 3).toNat := by
    have hh (b : Bool) : (if b then (1 : ℕ) else 0) = b.toNat := by cases b <;> rfl
    simp only [weight,Fin.sum_univ_four,hh]
  apply hx
  omega

/-- Exact arrow reversal identifies the opposite row with the conjugate row. -/
theorem ars_pairSlice (i j : Fin n) (hij : i ≠ j) (f : Signature AlgebraicComplex n)
    (hs : ARS f) (a b : Bool) (z : Remaining i j → Bool) :
    (pairSlice (K := AlgebraicComplex) i j hij f (!a) (!b) (fun k => !(z k)) : ℂ) =
      star (pairSlice (K := AlgebraicComplex) i j hij f a b z : ℂ) := by
  have hh := congrArg star (hs (fillPair i j hij a b z))
  simpa only [pairSlice,fillPair_complement,star_star] using hh.symm

noncomputable def sliceMass (i j : Fin n) (hij : i ≠ j) (f : Signature AlgebraicComplex n)
    (a b : Bool) : ℝ := ∑ z, Complex.normSq (pairSlice (K := AlgebraicComplex) i j hij f a b z : ℂ)

theorem sliceMass_nonneg (i j : Fin n) (hij : i ≠ j) (f : Signature AlgebraicComplex n)
    (a b : Bool) : 0 ≤ sliceMass i j hij f a b :=
  Finset.sum_nonneg (fun _ _ => Complex.normSq_nonneg _)

theorem sliceMass_complement (i j : Fin n) (hij : i ≠ j) (f : Signature AlgebraicComplex n)
    (hs : ARS f) (a b : Bool) : sliceMass i j hij f (!a) (!b) = sliceMass i j hij f a b := by
  classical
  unfold sliceMass
  rw [← (Equiv.piCongrRight (fun _ : Remaining i j => Equiv.boolNot)).sum_comp]
  apply Finset.sum_congr rfl
  intro z _
  change Complex.normSq (pairSlice (K := AlgebraicComplex) i j hij f (!a) (!b) (fun k => !(z k)) : ℂ) = _
  rw [ars_pairSlice i j hij f hs]
  exact Complex.normSq_conj _

theorem gramTable_norm (i j : Fin n) (hij : i ≠ j) (f : Signature AlgebraicComplex n)
    (hs : ARS f) (a b : Bool) :
    (gramTable (K := AlgebraicComplex) i j hij f (quadWord a b (!a) (!b)) : ℂ) = (sliceMass i j hij f a b : ℂ) := by
  rw [gramTable_coe]
  change (∑ z, (pairSlice (K := AlgebraicComplex) i j hij f a b z : ℂ) *
    (pairSlice (K := AlgebraicComplex) i j hij f (!a) (!b) (fun k => !(z k)) : ℂ)) = _
  simp_rw [ars_pairSlice i j hij f hs]
  simp only [Complex.star_def,Complex.mul_conj,sliceMass,Complex.ofReal_sum]

/-- A vanishing positive squared mass means the entire actual slice vanishes. -/
theorem sliceMass_eq_zero (i j : Fin n) (hij : i ≠ j) (f : Signature AlgebraicComplex n)
    (a b : Bool) (hz : sliceMass i j hij f a b = 0) :
    ∀ z, pairSlice (K := AlgebraicComplex) i j hij f a b z = 0 := by
  intro z
  have hh : Complex.normSq (pairSlice (K := AlgebraicComplex) i j hij f a b z : ℂ) ≤ sliceMass i j hij f a b :=
    by
      unfold sliceMass
      exact Finset.single_le_sum (f := fun w => Complex.normSq (pairSlice (K := AlgebraicComplex) i j hij f a b w : ℂ))
        (fun w _ => Complex.normSq_nonneg _) (Finset.mem_univ z)
  rw [hz] at hh
  exact Subtype.ext (Complex.normSq_eq_zero.mp (le_antisymm hh (Complex.normSq_nonneg _)))

/-- Mating a nonzero ARS table never produces the zero quaternary. -/
theorem gramTable_ne_zero (i j : Fin n) (hij : i ≠ j) (f : Signature AlgebraicComplex n)
    (hf : f ≠ 0) (hs : ARS f) : gramTable (K := AlgebraicComplex) i j hij f ≠ 0 := by
  intro hz
  apply hf
  funext x
  have hh := gramTable_norm i j hij f hs (x i) (x j)
  rw [hz] at hh
  have hmass : sliceMass i j hij f (x i) (x j) = 0 := by
    have hh' : (0 : ℂ) = (sliceMass i j hij f (x i) (x j) : ℂ) := hh
    exact_mod_cast hh'.symm
  have hval := sliceMass_eq_zero i j hij f (x i) (x j) hmass (fun k => x k.val)
  simpa only [pairSlice,fillPair_eta,Pi.zero_apply] using hval

noncomputable def gramCross (i j : Fin n) (hij : i ≠ j) (f : Signature AlgebraicComplex n) : ℂ :=
  ∑ z, (pairSlice (K := AlgebraicComplex) i j hij f false true z : ℂ) * star (pairSlice (K := AlgebraicComplex) i j hij f true false z : ℂ)

theorem gramTable_cross (i j : Fin n) (hij : i ≠ j) (f : Signature AlgebraicComplex n)
    (hs : ARS f) :
    (gramTable (K := AlgebraicComplex) i j hij f (quadWord false true false true) : ℂ) = gramCross i j hij f := by
  rw [gramTable_coe]
  unfold gramTable gramCross
  apply Finset.sum_congr rfl
  intro z _
  change (pairSlice (K := AlgebraicComplex) i j hij f false true z : ℂ) *
    (pairSlice (K := AlgebraicComplex) i j hij f (!true) (!false) (fun k => !(z k)) : ℂ) = _
  rw [ars_pairSlice i j hij f hs]

theorem gramTable_cross_star (i j : Fin n) (hij : i ≠ j) (f : Signature AlgebraicComplex n)
    (hs : ARS f) :
    (gramTable (K := AlgebraicComplex) i j hij f (quadWord true false true false) : ℂ) = star (gramCross i j hij f) := by
  rw [gramTable_coe]
  unfold gramTable gramCross
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro z _
  change (pairSlice (K := AlgebraicComplex) i j hij f true false z : ℂ) *
    (pairSlice (K := AlgebraicComplex) i j hij f (!false) (!true) (fun k => !(z k)) : ℂ) = _
  rw [ars_pairSlice i j hij f hs,star_mul,star_star]

end
end Paper2.RelativeEO
