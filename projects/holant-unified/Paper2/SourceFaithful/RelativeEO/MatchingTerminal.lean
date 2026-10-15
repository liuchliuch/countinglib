import Paper2.SourceFaithful.RelativeEO.BinaryEOAlternative
import Paper2.RelativeEO.MatchingFactors

namespace Paper2.SourceFaithful.RelativeEO
open Tractable ExactInput Paper2.RelativeEO

/-- A matching EO tensor outside B_ARS has an actual extracted binary outside
projective ARS; the complete binary alternative closes the original language. -/
theorem matching_relative_terminal (B : Paper1BinaryInterpolationAccepted)
    (F : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) {n : ℕ} (f : Signature AlgebraicComplex n)
    (hmem : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hmatch : WeightedMatching.IsProduct f) (hout : ¬ IsARSProduct f) :
    FixedFieldOutput.SharpPHard .nativeX L := by
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
    (eoSignature_ne_zero_left _ _ (hp j)) hEO (hfac j)).resolve_left hj).transport hNL


end Paper2.SourceFaithful.RelativeEO
