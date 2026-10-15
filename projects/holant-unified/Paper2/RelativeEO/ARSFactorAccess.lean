import Paper2.RelativeEO.MatchingFactors
import Paper2.MatchingPropagation.Basic

/-! The exact algebraic representatives and retained factor language consumed
by high-arity local normalization. A complex matching witness alone is never
used to adjoin arbitrary coefficients or a free binary attachment. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open scoped BigOperators

theorem IsARSProduct.reindex {m n : ℕ} {f : Signature AlgebraicComplex m}
    (h : IsARSProduct f) (e : Fin m ≃ Fin n) : IsARSProduct (Tensor.reindex e f) := by
  obtain ⟨P,a,c,hc,ha,hf⟩ := h
  exact ⟨⟨P.count,P.ports.trans e⟩,a,c,hc,ha,by rw [hf]; rfl⟩

/-- Coercion retains the actual algebraic factors, matching, and scalar. -/
theorem IsARSProduct.coe {n : ℕ} {f : Signature AlgebraicComplex n}
    (h : IsARSProduct f) : MatchingPropagation.IsARS (fun x => (f x : ℂ)) := by
  obtain ⟨P,a,c,hc,ha,hf⟩ := h
  refine ⟨CommonPhase.ofPairing P,(fun j => (a j : ℂ)),(c : ℂ),?_,?_,?_⟩
  · exact_mod_cast hc
  · intro j; change (a j : ℂ) ≠ 0; exact_mod_cast ha j
  · rw [hf]
    funext x
    let φ : AlgebraicComplex →+* ℂ := (algebraicClosure ℚ ℂ).val.toRingHom
    change φ (c * ∏ j, WeightedMatching.binary (a j) (conjugateAlgebraic (a j))
      (x (P.ports (j,false))) (x (P.ports (j,true)))) = _
    rw [map_mul,map_prod]
    change (c : ℂ) * _ = (c : ℂ) * _
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    change φ (WeightedMatching.binary (a j) (conjugateAlgebraic (a j))
      (x (P.ports (j,false))) (x (P.ports (j,true)))) =
      WeightedMatching.binary (a j : ℂ) (star (a j : ℂ))
        (x (P.ports (j,false))) (x (P.ports (j,true)))
    cases x (P.ports (j,false)) <;> cases x (P.ports (j,true)) <;> rfl

/-- Extract every displayed algebraic EO–ARS binary as an actual literal member
of a finite retained language, with genuine reductions in both directions. -/
theorem arsMatching_factors_access (F : Paper1FactorClosureAccepted)
    (L : Language) (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    {n : ℕ} (P : OrientedPerfectPairing n) (a : Fin P.count → AlgebraicComplex)
    (c : AlgebraicComplex) (hc : c ≠ 0) (ha : ∀ j, a j ≠ 0)
    (hmem : (⟨n,WeightedMatching.product P a (fun j => conjugateAlgebraic (a j)) c⟩ :
      AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ N : Language, L.family ⊆ N.family ∧ Preprocessed N.family ∧
      (∀ j, (⟨2,eoSignature (a j) (conjugateAlgebraic (a j))⟩ : AnySignature AlgebraicComplex) ∈ N.family) ∧
      Reduces .nativeX N L ∧ Reduces .nativeX L N := by
  let D := matchingDecomposition P a (fun j => conjugateAlgebraic (a j)) c hc
  obtain ⟨N,hLN,hfac,hpreN,_,hNL,hLN'⟩ := factorClosure_with_member_decomposition F L hpre htwo _ hmem
    D (matchingDecomposition_value P a (fun j => conjugateAlgebraic (a j)) c hc)
    (fun _ => by change 0 < (2 : ℕ); decide)
    (matchingDecomposition_prime P a (fun j => conjugateAlgebraic (a j)) c hc ha
      (fun j => conjugateAlgebraic_ne_zero.mpr (ha j)))
  exact ⟨N,hLN,hpreN,hfac,hNL,hLN'⟩

/-- The existential source witness is exposed together with its actual
retained extraction, so a client need not choose a complex representative. -/
theorem arsProduct_factors_access (F : Paper1FactorClosureAccepted)
    (L : Language) (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    {n : ℕ} (f : Signature AlgebraicComplex n)
    (hmem : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hars : IsARSProduct f) :
    ∃ (P : OrientedPerfectPairing n) (a : Fin P.count → AlgebraicComplex)
      (c : AlgebraicComplex) (N : Language),
      c ≠ 0 ∧ (∀ j, a j ≠ 0) ∧
      f = WeightedMatching.product P a (fun j => conjugateAlgebraic (a j)) c ∧
      L.family ⊆ N.family ∧ Preprocessed N.family ∧
      (∀ j, (⟨2,eoSignature (a j) (conjugateAlgebraic (a j))⟩ : AnySignature AlgebraicComplex) ∈ N.family) ∧
      Reduces .nativeX N L ∧ Reduces .nativeX L N := by
  obtain ⟨P,a,c,hc,ha,hform⟩ := hars
  obtain ⟨N,hLN,hpreN,hfac,hNL,hLN'⟩ := arsMatching_factors_access F L hpre htwo P a c hc ha (hform ▸ hmem)
  exact ⟨P,a,c,N,hc,ha,hform,hLN,hpreN,hfac,hNL,hLN'⟩

end Paper2.RelativeEO
