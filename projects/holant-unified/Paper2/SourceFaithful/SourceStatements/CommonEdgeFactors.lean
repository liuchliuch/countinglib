import Paper2.SourceFaithful.SourceStatements.MatchingCommonEdge
import Paper2.SourceFaithful.SourceStatements.ThreeMatchingLine

/-! Literal factor agreement outside the four-cycle branch of source 5.15.
The intersection cancellation and its nonzero witnesses follow from the three
original matching products. Endpoint reversals and all outside scalars remain
in their original presentations. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
namespace Paper2.SourceFaithful.SourceStatements
noncomputable section
open Holant Holant.Marked Holant.Certificates
open Holant.Dihedral.CompatibleClosure Holant.Dihedral.EndpointParallelogram
open Holant.Dihedral.CompatibleCoefficientLine Holant.Dihedral.TwoCardLocalization
open Holant.Dihedral.SectorRuling
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {s n : ℕ}

private def edgeRemainder (p₀ p : (Fin s × Bool) ≃ Fin n)
    (A : Fin s → Mat) (κ : Scalar) (e : Fin s) (x : Fin n → Bool) : Scalar :=
  κ * ∏ d ∈ ({(p.symm (p₀ (e,false))).1}ᶜ : Finset (Fin s)),
    A d (x (p (d,false))) (x (p (d,true)))

private theorem monomial_support_at_point (A B : Mat)
    (hA : IsMonomial A) (hB : IsMonomial B) (u v : Bool)
    (ha : A u v ≠ 0) (hb : B u v ≠ 0) :
    ∀ a b, A a b ≠ 0 ↔ B a b ≠ 0 := by
  obtain ⟨α,w,hw,hAe⟩ := hA
  obtain ⟨β,t,ht,hBe⟩ := hB
  have hα : v = Bool.xor u α := by
    by_contra h
    exact ha (by simp [hAe,monomial,h])
  have hβ : v = Bool.xor u β := by
    by_contra h
    exact hb (by simp [hBe,monomial,h])
  have hab : α = β := by
    cases u <;> cases α <;> cases β <;> simp_all
  subst β
  intro a b
  simp [hAe,hBe,monomial,hw,ht]

private theorem common_edge_first_factor
    (p₀ p₁ p₂ : (Fin s × Bool) ≃ Fin n)
    (A₀ A₁ A₂ : Fin s → Mat) (κ₀ κ₁ κ₂ a b : Scalar)
    (hA₀ : ∀ e, IsMonomial (A₀ e)) (hA₁ : ∀ e, IsMonomial (A₁ e))
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hrel : productValue p₂ A₂ κ₂ =
      combination a b (productValue p₀ A₀ κ₀) (productValue p₁ A₁ κ₁))
    (hcommon : (support (coefficients (productValue p₀ A₀ κ₀)) ∩
      support (coefficients (productValue p₁ A₁ κ₁))).Nonempty)
    (hcancel : ∀ z ∈ support (coefficients (productValue p₀ A₀ κ₀)) ∩
      support (coefficients (productValue p₁ A₁ κ₁)), coefficients (productValue p₂ A₂ κ₂) z = 0)
    (e : Fin s)
    (hm : (Pairing.ofPorts p₁).mate (p₀ (e,false)) = p₀ (e,true)) :
    ProjectivelyEqual (relativeFactor p₀ p₁ A₁ e) (A₀ e) := by
  classical
  obtain ⟨z,hz⟩ := hcommon
  let x := (bitsEquiv (Fin n)).symm z
  have hx₀ : productValue p₀ A₀ κ₀ x ≠ 0 := by
    exact (mem_support (coefficients (productValue p₀ A₀ κ₀)) z).mp (Finset.mem_inter.mp hz).1
  have hx₁ : productValue p₁ A₁ κ₁ x ≠ 0 := by
    exact (mem_support (coefficients (productValue p₁ A₁ κ₁)) z).mp (Finset.mem_inter.mp hz).2
  let R₀ : Scalar := κ₀ * ∏ d ∈ ({e}ᶜ : Finset (Fin s)),
    A₀ d (x (p₀ (d,false))) (x (p₀ (d,true)))
  let R₁ := edgeRemainder p₀ p₁ A₁ κ₁ e x
  have hself : MatchingContractionClosure.insertPair (p₀ (e,false)) (p₀ (e,true))
      (x (p₀ (e,false))) (x (p₀ (e,true))) x = x := by
    simp [MatchingContractionClosure.insertPair]
  have hslice₀ : productValue p₀ A₀ κ₀ x =
      A₀ e (x (p₀ (e,false))) (x (p₀ (e,true))) * R₀ := by
    have h := MatchingContractionClosure.product_extract_edge p₀ A₀ κ₀ e
      (x (p₀ (e,false))) (x (p₀ (e,true))) x
    rw [hself] at h
    exact h
  have hslice₁ : productValue p₁ A₁ κ₁ x =
      relativeFactor p₀ p₁ A₁ e (x (p₀ (e,false))) (x (p₀ (e,true))) * R₁ := by
    have h := common_edge_extract p₀ p₁ A₁ κ₁ e hm
      (x (p₀ (e,false))) (x (p₀ (e,true))) x
    rw [hself] at h
    exact h
  have hR₀ : R₀ ≠ 0 := (mul_ne_zero_iff.mp (hslice₀ ▸ hx₀)).2
  have hR₁ : R₁ ≠ 0 := (mul_ne_zero_iff.mp (hslice₁ ▸ hx₁)).2
  have hsupport := monomial_support_at_point (A₀ e) (relativeFactor p₀ p₁ A₁ e)
    (hA₀ e) (relativeFactor_isMonomial p₀ p₁ A₁ hA₁ e)
    (x (p₀ (e,false))) (x (p₀ (e,true)))
    (mul_ne_zero_iff.mp (hslice₀ ▸ hx₀)).1 (mul_ne_zero_iff.mp (hslice₁ ▸ hx₁)).1
  have hv (u v : Bool) : a * (A₀ e u v * R₀) +
      b * (relativeFactor p₀ p₁ A₁ e u v * R₁) = 0 := by
    by_cases hu : A₀ e u v ≠ 0
    · let y := MatchingContractionClosure.insertPair (p₀ (e,false)) (p₀ (e,true)) u v x
      have hy₀ : productValue p₀ A₀ κ₀ y ≠ 0 := by
        change MatchingContractionClosure.productValue p₀ A₀ κ₀ _ ≠ 0
        rw [MatchingContractionClosure.product_extract_edge]
        exact mul_ne_zero hu hR₀
      have hy₁ : productValue p₁ A₁ κ₁ y ≠ 0 := by
        rw [common_edge_extract p₀ p₁ A₁ κ₁ e hm u v x]
        exact mul_ne_zero ((hsupport u v).mp hu) hR₁
      have hy : bitsEquiv (Fin n) y ∈ support (coefficients (productValue p₀ A₀ κ₀)) ∩
          support (coefficients (productValue p₁ A₁ κ₁)) := by
        apply Finset.mem_inter.mpr
        constructor <;> simpa only [mem_support,coefficients,Equiv.symm_apply_apply] using (by assumption)
      have hz₂ : productValue p₂ A₂ κ₂ y = 0 := by
        simpa only [coefficients,Equiv.symm_apply_apply] using hcancel _ hy
      have h := congrFun hrel y
      change productValue p₂ A₂ κ₂ y = a * productValue p₀ A₀ κ₀ y +
        b * productValue p₁ A₁ κ₁ y at h
      rw [hz₂] at h
      change 0 = a * MatchingContractionClosure.productValue p₀ A₀ κ₀ _ +
        b * productValue p₁ A₁ κ₁ _ at h
      rw [MatchingContractionClosure.product_extract_edge,
        common_edge_extract p₀ p₁ A₁ κ₁ e hm u v x] at h
      exact h.symm
    · have hu' : A₀ e u v = 0 := not_ne_iff.mp hu
      have hv' : relativeFactor p₀ p₁ A₁ e u v = 0 := by
        by_contra hn
        exact hu ((hsupport u v).mpr hn)
      rw [hu',hv']
      ring
  refine ⟨-(a*R₀)/(b*R₁),div_ne_zero (neg_ne_zero.mpr (mul_ne_zero ha hR₀))
    (mul_ne_zero hb hR₁),?_⟩
  funext u v
  change relativeFactor p₀ p₁ A₁ e u v = (-(a*R₀)/(b*R₁)) * A₀ e u v
  field_simp [hb,hR₁]
  linear_combination hv u v

/-- A common original matched edge whose first two factor lines agree retains
that line in the third actual nonzero matching product, even if the other
original edges have different pairings. -/
theorem common_edge_third_factor
    (p₀ p₁ p₂ : (Fin s × Bool) ≃ Fin n)
    (A₀ A₁ A₂ : Fin s → Mat) (κ₀ κ₁ κ₂ a b : Scalar)
    (hA₂ : ∀ e, IsMonomial (A₂ e)) (hκ₂ : κ₂ ≠ 0)
    (hrel : productValue p₂ A₂ κ₂ =
      combination a b (productValue p₀ A₀ κ₀) (productValue p₁ A₁ κ₁))
    (e : Fin s)
    (hm₁ : (Pairing.ofPorts p₁).mate (p₀ (e,false)) = p₀ (e,true))
    (hm₂ : (Pairing.ofPorts p₂).mate (p₀ (e,false)) = p₀ (e,true))
    (he : ProjectivelyEqual (relativeFactor p₀ p₁ A₁ e) (A₀ e)) :
    ProjectivelyEqual (relativeFactor p₀ p₂ A₂ e) (A₀ e) := by
  classical
  obtain ⟨c,hc,hcEq⟩ := he
  let x := supportedWord p₂ A₂ hA₂
  let R₀ : Scalar := κ₀ * ∏ d ∈ ({e}ᶜ : Finset (Fin s)),
    A₀ d (x (p₀ (d,false))) (x (p₀ (d,true)))
  let R₁ := edgeRemainder p₀ p₁ A₁ κ₁ e x
  let R₂ := edgeRemainder p₀ p₂ A₂ κ₂ e x
  let T := a * R₀ + b * c * R₁
  have hR₂ : R₂ ≠ 0 := mul_ne_zero hκ₂
    (Finset.prod_ne_zero_iff.mpr (fun d _ => supportedWord_factor p₂ A₂ hA₂ d))
  have hv (u v : Bool) : relativeFactor p₀ p₂ A₂ e u v * R₂ = A₀ e u v * T := by
    have h := congrFun hrel (MatchingContractionClosure.insertPair
      (p₀ (e,false)) (p₀ (e,true)) u v x)
    change productValue p₂ A₂ κ₂ _ =
      a * MatchingContractionClosure.productValue p₀ A₀ κ₀ _ + b * productValue p₁ A₁ κ₁ _ at h
    rw [common_edge_extract p₀ p₂ A₂ κ₂ e hm₂ u v x,
      MatchingContractionClosure.product_extract_edge,
      common_edge_extract p₀ p₁ A₁ κ₁ e hm₁ u v x] at h
    rw [hcEq] at h
    change relativeFactor p₀ p₂ A₂ e u v * R₂ =
      a * (A₀ e u v * R₀) + b * (c * A₀ e u v * R₁) at h
    rw [h]
    dsimp only [T]
    ring
  have hpoint : relativeFactor p₀ p₂ A₂ e (x (p₀ (e,false))) (x (p₀ (e,true))) ≠ 0 := by
    have hself : MatchingContractionClosure.insertPair (p₀ (e,false)) (p₀ (e,true))
        (x (p₀ (e,false))) (x (p₀ (e,true))) x = x := by
      simp [MatchingContractionClosure.insertPair]
    have hx : productValue p₂ A₂ κ₂ x ≠ 0 := mul_ne_zero hκ₂
      (Finset.prod_ne_zero_iff.mpr (fun d _ => supportedWord_factor p₂ A₂ hA₂ d))
    have h := common_edge_extract p₀ p₂ A₂ κ₂ e hm₂
      (x (p₀ (e,false))) (x (p₀ (e,true))) x
    rw [hself] at h
    exact (mul_ne_zero_iff.mp (h ▸ hx)).1
  have hT : T ≠ 0 := by
    have h := mul_ne_zero hpoint hR₂
    rw [hv] at h
    exact (mul_ne_zero_iff.mp h).2
  refine ⟨T/R₂,div_ne_zero hT hR₂,?_⟩
  funext u v
  change relativeFactor p₀ p₂ A₂ e u v = (T/R₂) * A₀ e u v
  field_simp [hR₂]
  linear_combination hv u v

/-- The common factors in the different-support branch of source 5.15 are
derived from the complete original coefficient relation. Only original mate
agreement on the queried edge is required from the four-cycle geometry. -/
theorem different_support_common_edge_factors
    (p₀ p₁ p₂ : (Fin s × Bool) ≃ Fin n)
    (A₀ A₁ A₂ : Fin s → Mat) (κ₀ κ₁ κ₂ a b : Scalar)
    (hA₀ : ∀ e, IsMonomial (A₀ e)) (hA₁ : ∀ e, IsMonomial (A₁ e))
    (hA₂ : ∀ e, IsMonomial (A₂ e))
    (hκ₀ : κ₀ ≠ 0) (hκ₁ : κ₁ ≠ 0) (hκ₂ : κ₂ ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hne : support (coefficients (productValue p₀ A₀ κ₀)) ≠
      support (coefficients (productValue p₁ A₁ κ₁)))
    (hrel : productValue p₂ A₂ κ₂ =
      combination a b (productValue p₀ A₀ κ₀) (productValue p₁ A₁ κ₁))
    (e : Fin s)
    (hm₁ : (Pairing.ofPorts p₁).mate (p₀ (e,false)) = p₀ (e,true))
    (hm₂ : (Pairing.ofPorts p₂).mate (p₀ (e,false)) = p₀ (e,true)) :
    ProjectivelyEqual (relativeFactor p₀ p₁ A₁ e) (A₀ e) ∧
      ProjectivelyEqual (relativeFactor p₀ p₂ A₂ e) (A₀ e) := by
  obtain ⟨_,_,hcommon,hcancel⟩ := different_support_three_matching_products
    p₀ p₁ p₂ A₀ A₁ A₂ κ₀ κ₁ κ₂ a b hA₀ hA₁ hA₂ hκ₀ hκ₁ hκ₂ ha hb hne hrel
  have he := common_edge_first_factor p₀ p₁ p₂ A₀ A₁ A₂ κ₀ κ₁ κ₂ a b
    hA₀ hA₁ ha hb hrel hcommon hcancel e hm₁
  exact ⟨he,common_edge_third_factor p₀ p₁ p₂ A₀ A₁ A₂ κ₀ κ₁ κ₂ a b
    hA₂ hκ₂ hrel e hm₁ hm₂ he⟩

end
end Paper2.SourceFaithful.SourceStatements

