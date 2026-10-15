import Paper2.RelativeEO.BinaryPrime
import Paper2.RelativeEO.WeightedComplementaryExit

/-! Exact algebraic matching factors, their ARS rescaling, and legitimate
retained extraction. These lemmas use no singleton EO theorem on an ambient
language and do not conflate a coordinate slice with a realizable signature. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open scoped BigOperators

/-- The coefficient form of projective ARS on a nonzero EO binary. -/
theorem binary_ars_coefficients (p q : AlgebraicComplex) (hp : p ≠ 0)
    (h : ProjectiveARS (eoSignature p q)) :
    ∃ c a : AlgebraicComplex, c ≠ 0 ∧ a ≠ 0 ∧ p = c*a ∧ q = c*conjugateAlgebraic a := by
  obtain ⟨c,hc,h⟩ := h
  let a := c⁻¹*p
  have ha : a ≠ 0 := mul_ne_zero (inv_ne_zero hc) hp
  have he : (fun i => !(binWord true false i)) = binWord false true := by
    funext i; fin_cases i <;> rfl
  have hq : c⁻¹*q = conjugateAlgebraic a := by
    apply Subtype.ext
    change (c : ℂ)⁻¹*(q : ℂ) = star ((c : ℂ)⁻¹*(p : ℂ))
    have hh := h (binWord true false)
    rw [he] at hh
    exact hh
  refine ⟨c,a,hc,ha,?_,?_⟩
  · dsimp [a]
    rw [← mul_assoc,mul_inv_cancel₀ hc,one_mul]
  · rw [← hq,← mul_assoc,mul_inv_cancel₀ hc,one_mul]

/-- Rescaling all matching factors keeps one actual algebraic overall scalar. -/
theorem matching_isARSProduct {n : ℕ} (P : OrientedPerfectPairing n)
    (p q : Fin P.count → AlgebraicComplex) (c : AlgebraicComplex) (hc : c ≠ 0)
    (hp : ∀ j, p j ≠ 0) (hars : ∀ j, ProjectiveARS (eoSignature (p j) (q j))) :
    IsARSProduct (WeightedMatching.product P p q c) := by
  classical
  choose s a hs ha hp' hq' using fun j => binary_ars_coefficients (p j) (q j) (hp j) (hars j)
  refine ⟨P,a,c*(∏ j,s j),mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr (fun j _ => hs j)),ha,?_⟩
  funext x
  have hfac (j : Fin P.count) (u v : Bool) :
      WeightedMatching.binary (p j) (q j) u v =
        s j * WeightedMatching.binary (a j) (conjugateAlgebraic (a j)) u v := by
    cases u <;> cases v <;> simp [WeightedMatching.binary,hp',hq']
  simp only [WeightedMatching.product,hfac,Finset.prod_mul_distrib]
  ring

/-- The literal finite decomposition on precisely the oriented matching ports. -/
noncomputable def matchingDecomposition {n : ℕ} (P : OrientedPerfectPairing n)
    (p q : Fin P.count → AlgebraicComplex) (c : AlgebraicComplex) (hc : c ≠ 0) :
    TensorDecomposition AlgebraicComplex n where
  count := P.count
  arity _ := 2
  factor j := eoSignature (p j) (q j)
  ports := ((Equiv.sigmaEquivProd (Fin P.count) (Fin 2)).trans
    (Equiv.prodCongr (Equiv.refl _) finTwoEquiv)).trans P.ports
  scale := Units.mk0 c hc

theorem matchingDecomposition_value {n : ℕ} (P : OrientedPerfectPairing n)
    (p q : Fin P.count → AlgebraicComplex) (c : AlgebraicComplex) (hc : c ≠ 0) :
    (matchingDecomposition P p q c hc).value = WeightedMatching.product P p q c := by
  funext x
  unfold TensorDecomposition.value WeightedMatching.product
  congr 1

/-- Every nonzero displayed matching factor is an actual prime factor. -/
theorem matchingDecomposition_prime {n : ℕ} (P : OrientedPerfectPairing n)
    (p q : Fin P.count → AlgebraicComplex) (c : AlgebraicComplex) (hc : c ≠ 0)
    (hp : ∀ j, p j ≠ 0) (hq : ∀ j, q j ≠ 0) :
    ∀ j, TensorPrime ((matchingDecomposition P p q c hc).factor j) :=
  fun j => eoSignature_tensorPrime (p j) (q j) (hp j) (hq j)

/-- A matching EO tensor outside B_ARS has an actual extracted binary outside
projective ARS; the complete binary alternative closes the original language. -/
theorem matching_relative_terminal (B : Paper1BinaryInterpolationAccepted)
    (F : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) {n : ℕ} (f : Signature AlgebraicComplex n)
    (hmem : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hmatch : WeightedMatching.IsProduct f) (hout : ¬ IsARSProduct f) :
    SharpPHard .nativeX L := by
  classical
  obtain ⟨P,p,q,c,hn,hform⟩ := hmatch
  obtain ⟨hc,hp,hq⟩ := WeightedMatching.parameters_nonzero P p q c hn
  have hex : ∃ j, ¬ ProjectiveARS (eoSignature (p j) (q j)) := by
    by_contra h
    push Not at h
    exact hout (hform.symm ▸ matching_isARSProduct P p q c hc hp h)
  obtain ⟨j,hj⟩ := hex
  let D := matchingDecomposition P p q c hc
  obtain ⟨N,hLN,hfac,hpreN,_,hNL,_⟩ := factorClosure_with_member_decomposition F L hpre
    (bothChargeSigns_not_oneSided hboth) f hmem D
    ((matchingDecomposition_value P p q c hc).trans hform.symm)
    (fun _ => by change 0 < (2 : ℕ); decide) (matchingDecomposition_prime P p q c hc hp hq)
  have hbothN : BothChargeSigns N.family := by
    obtain ⟨⟨f,hf,x,hx,hn⟩,⟨g,hg,y,hy,hp⟩⟩ := hboth
    exact ⟨⟨f,hLN hf,x,hx,hn⟩,⟨g,hLN hg,y,hy,hp⟩⟩
  have hnotN : ¬ Tract (kImage N) := fun ht =>
    hnot (ht.mono_family (familyAction_mono sourceKBasis hLN))
  have hEO : Signature.CentralSupport (eoSignature (p j) (q j)) := by
    intro x hx
    have hb : ∀ y : Fin 2 → Bool, 2 * weight y ≠ 2 → y 0 = y 1 := by decide +kernel
    have hx' : x 0 = x 1 := hb x hx
    cases h0 : x 0 <;> cases h1 : x 1 <;> simp_all [eoSignature,matrixSignature,eoMatrix]
  exact ((binary_eo_alternative B F U N hpreN hbothN hnotN _
    (eoSignature_ne_zero_left _ _ (hp j)) hEO (hfac j)).resolve_left hj).transport_unconditional hNL

end Paper2.RelativeEO
