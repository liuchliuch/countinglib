import Paper2.SourceFaithful.FactorClosure
import Paper2.RelativeEO.ARSFactorAccess
import Paper2.HeightThree.Preservation

/-! Selective finite factor extraction for the high-height normalization.
The full prime-factor language is used only as an intermediate oracle.  The
retained language contains precisely the original labels and the selected
binary factors, so unrelated prime factors cannot invalidate the ambient
even-arity and charge-divisibility hypotheses. -/
namespace Paper2.SourceFaithful.HighHeight
open Tractable ExactInput Paper2.RelativeEO

noncomputable def selectedFactors {n : ℕ}
    (Q : TensorDecomposition AlgebraicComplex n) : SignatureFamily AlgebraicComplex :=
  Set.range (fun j => (⟨Q.arity j,Q.factor j⟩ : AnySignature AlgebraicComplex))

/-- Extract a prescribed actual prime decomposition and immediately restrict
to its selected factors.  Every new table is justified by the Paper 1 factor
reduction; the intermediate full factor closure is not retained. -/
theorem selected_factor_augmentation
    (F : Paper1FactorClosureAccepted) (R : Paper1RestrictionAccepted)
    (L : Language) (hpre : Preprocessed L.family)
    (htwo : ¬ CommonOneSided L.family) {n : ℕ}
    (f : Signature AlgebraicComplex n)
    (hmem : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (Q : TensorDecomposition AlgebraicComplex n) (hQ : Q.value = f)
    (hp : ∀ j, 0 < Q.arity j) (ht : ∀ j, TensorPrime (Q.factor j)) :
    ∃ N : Language,
      N.family = L.family ∪ selectedFactors Q ∧
      Preprocessed N.family ∧
      FixedFieldOutput.Reduces .nativeX N L ∧
      FixedFieldOutput.Reduces .nativeX L N := by
  obtain ⟨A,hLA,hfac,hpreA,_,hAL,_⟩ :=
    factorClosure_with_member_decomposition F L hpre htwo f hmem Q hQ hp ht
  have hfinite : (L.family ∪ selectedFactors Q).Finite :=
    L.family_finite.union (Set.finite_range _)
  obtain ⟨N,hN⟩ := Language.coverage_family _ hfinite
  have hNA : N.family ⊆ A.family := by
    intro g hg
    rw [hN] at hg
    rcases hg with hg | ⟨j,rfl⟩
    · exact hLA hg
    · exact hfac j
  have hLN : L.family ⊆ N.family := by
    rw [hN]
    exact Set.subset_union_left
  exact ⟨N,hN,(fun g hg => hpreA g (hNA hg)),
    (R.restriction_2_5 N A hNA).trans hAL,R.restriction_2_5 L N hLN⟩

/-- The ordered nonsingular EO binary is genuinely central on both ports. -/
theorem ars_binary_eo (z : AlgebraicComplex) :
    IsEO (⟨2,eoSignature z (conjugateAlgebraic z)⟩ : AnySignature AlgebraicComplex) := by
  refine ⟨⟨1,rfl⟩,?_⟩
  intro x hx
  have hb : ∀ y : Fin 2 → Bool, 2 * weight y ≠ 2 → y 0 = y 1 := by
    decide +kernel
  have he := hb x hx
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp_all [eoSignature,matrixSignature,eoMatrix]

/-- All displayed ARS factors are literal algebraic tables in a selective
finite extension.  In particular every new label is even and EO, so every
pre-existing half-charge divisor is retained. -/
theorem ars_factors_retained
    (F : Paper1FactorClosureAccepted) (R : Paper1RestrictionAccepted)
    (L : Language) (hpre : Preprocessed L.family)
    (htwo : ¬ CommonOneSided L.family) {n : ℕ}
    (f : Signature AlgebraicComplex n)
    (hmem : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hars : IsARSProduct f) :
    ∃ (P : OrientedPerfectPairing n) (z : Fin P.count → AlgebraicComplex)
      (c : AlgebraicComplex) (N : Language),
      c ≠ 0 ∧ (∀ j, z j ≠ 0) ∧
      f = WeightedMatching.product P z (fun j => conjugateAlgebraic (z j)) c ∧
      N.family = L.family ∪ Set.range
        (fun j => (⟨2,eoSignature (z j) (conjugateAlgebraic (z j))⟩ : AnySignature AlgebraicComplex)) ∧
      L.family ⊆ N.family ∧
      (∀ j, (⟨2,eoSignature (z j) (conjugateAlgebraic (z j))⟩ : AnySignature AlgebraicComplex) ∈ N.family) ∧
      Preprocessed N.family ∧ ¬ CommonOneSided N.family ∧
      (BothChargeSigns L.family → BothChargeSigns N.family) ∧
      (¬ Tract (kImage L) → ¬ Tract (kImage N)) ∧
      ((∀ g ∈ L.family, Even g.1) → ∀ g ∈ N.family, Even g.1) ∧
      (∀ d : ℤ, (∀ g ∈ L.family, Tensor.HalfChargeDivisible g.2 d) →
        ∀ g ∈ N.family, Tensor.HalfChargeDivisible g.2 d) ∧
      FixedFieldOutput.Reduces .nativeX N L ∧ FixedFieldOutput.Reduces .nativeX L N := by
  obtain ⟨P,z,c,hc,hz,hform⟩ := hars
  let Q := matchingDecomposition P z (fun j => conjugateAlgebraic (z j)) c hc
  obtain ⟨N,hN,hpreN,hNL,hLN'⟩ := selected_factor_augmentation F R L hpre htwo f hmem Q
    ((matchingDecomposition_value P z (fun j => conjugateAlgebraic (z j)) c hc).trans hform.symm)
    (fun _ => by change 0 < (2 : ℕ); decide)
    (matchingDecomposition_prime P z (fun j => conjugateAlgebraic (z j)) c hc hz
      (fun j => conjugateAlgebraic_ne_zero.mpr (hz j)))
  have hN' : N.family = L.family ∪ Set.range
      (fun j => (⟨2,eoSignature (z j) (conjugateAlgebraic (z j))⟩ : AnySignature AlgebraicComplex)) := hN
  have hLN : L.family ⊆ N.family := by rw [hN']; exact Set.subset_union_left
  refine ⟨P,z,c,N,hc,hz,hform,hN',hLN,?_,hpreN,?_,?_,?_,?_,?_,hNL,hLN'⟩
  · intro j
    rw [hN']
    exact Or.inr ⟨j,rfl⟩
  · intro hs
    apply htwo
    rcases hs with hs | hs
    · exact Or.inl (fun g hg => hs g (hLN hg))
    · exact Or.inr (fun g hg => hs g (hLN hg))
  · intro hb
    obtain ⟨⟨g,hg,x,hx,hn⟩,⟨h,hh,y,hy,hp⟩⟩ := hb
    exact ⟨⟨g,hLN hg,x,hx,hn⟩,⟨h,hLN hh,y,hy,hp⟩⟩
  · exact Paper2.HeightThree.retained_nontractable L N hLN
  · intro heven g hg
    rw [hN'] at hg
    rcases hg with hg | ⟨j,rfl⟩
    · exact heven g hg
    · exact even_two
  · intro d hdiv g hg
    rw [hN'] at hg
    rcases hg with hg | ⟨j,rfl⟩
    · exact hdiv g hg
    · exact Paper2.HeightThree.eo_halfCharge_divisible _ (ars_binary_eo (z j)) d

end Paper2.SourceFaithful.HighHeight
