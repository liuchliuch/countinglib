import Paper2.SourceFaithful.HeightThree.NonMatching
import Paper2.HeightThree.Preservation
import Paper2.SourceFaithful.RelativeEO.QuaternaryTerminal
import Paper2.Tractable.Conformal.CommonBasis
import Paper2.Tractable.CriteriaFacts


/-! Paper2 Theorem 7.1 for the original finite exact algebraic language.
The finite Q6 certificate, its complete orbit naturality, the real native-X
networks, and the arity-four ambient EO terminal are all proved in this project.
Only the explicitly named exact Paper1 results are accepted parameters.
All machine statements here use canonical fixed-field answers; no conversion
to isolated-root output codes or old strict-root classification is assumed. -/
namespace Paper2.SourceFaithful.HeightThree
open Tractable ExactInput Paper2.HeightThree

/-- The nonmatching output of Theorem 7.5 closes the preprocessed original
language through the proved local quaternary terminal. The argument actually
needs no ambient parity or charge-divisibility promise. -/
theorem mountain_classification_preprocessed
    (G : Paper1DirectGadgetAccepted) (O : Paper1OccurrenceAccepted)
    (F : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted)
    (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (L : Language) (hpre : Preprocessed L.family)
    (M : Signature AlgebraicComplex 6) (hM : IsMountain (d := 3) M)
    (hmem : (⟨6,M⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  by_cases ht : Tract (kImage L)
  · exact Or.inl ht
  · right
    obtain ⟨h,A,hn,he,hm,hA,hAL⟩ := adjoin_nonmatching_mountain G L M hM hmem
    have hLA : L.family ⊆ A.family := by rw [hA]; exact Set.subset_insert _ _
    have hpreA : Preprocessed A.family := by
      rw [hA]
      exact insert_nonzero_positive_preprocessed L.family ⟨4,h⟩ (by change 0 < (4 : ℕ); decide) hn hpre
    have hboth : BothChargeSigns A.family :=
      (commonOneSided_or_bothChargeSigns A.family).resolve_left
        (mountain_not_commonOneSided A.family (d := 3) M hM (hLA hmem))
    have hnotA : ¬ Tract (kImage A) := retained_nontractable L A hLA ht
    have hhmem : (⟨4,h⟩ : AnySignature AlgebraicComplex) ∈ A.family := by
      rw [hA]
      exact Set.mem_insert _ _
    exact (Paper2.SourceFaithful.RelativeEO.quaternary_nonmatching_terminal G O F U E R A hpreA hboth
      hnotA h hn he.2 hhmem hm).transport hAL

/-- Zero and nullary labels are allowed in the original problem. Classification
alone passes to its exact preprocessed subfamily; actual hardness returns by
literal restriction and canonical fixed-field oracle composition. -/
theorem mountain_classification
    (G : Paper1DirectGadgetAccepted) (O : Paper1OccurrenceAccepted)
    (F : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted)
    (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (L : Language) (M : Signature AlgebraicComplex 6)
    (hM : IsMountain (d := 3) M)
    (hmem : (⟨6,M⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨N,hN⟩ := Language.coverage_family (preprocess L.family)
    (L.family_finite.subset (fun _ h => h.1))
  have hpre : Preprocessed N.family := by rw [hN]; exact preprocess_preprocessed _
  have hmemN : (⟨6,M⟩ : AnySignature AlgebraicComplex) ∈ N.family := by
    rw [hN]
    refine ⟨hmem,by change 0 < 6; decide,?_⟩
    intro hz
    exact hM.zero_ne_zero (congrFun hz _)
  rcases mountain_classification_preprocessed G O F U E R N hpre M hM hmemN with ht | hh
  · left
    have hp : Tract (kImage N) ↔ Tract (kImage L) := by
      simp only [kImage,hN,← Conformal.preprocess_familyAction]
      exact tract_preprocess _
    exact hp.mp ht
  · exact Or.inr (hh.transport
      (R.restriction_2_5 N L (by rw [hN]; exact fun _ h => h.1)))

/-- The exact source height-three statement, with all ambient even-arity and
supported-half-charge hypotheses visible. The stronger local construction
above establishes the conclusion without needing to consume those promises. -/
theorem theorem_7_1
    (G : Paper1DirectGadgetAccepted) (O : Paper1OccurrenceAccepted)
    (F : Paper1FactorClosureAccepted) (U : Paper1UnaryAccepted)
    (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (L : Language) (_heven : ∀ f ∈ L.family, Even f.1)
    (_hdiv : ∀ f ∈ L.family, Tensor.HalfChargeDivisible f.2 3)
    (M : Signature AlgebraicComplex 6) (hM : IsMountain (d := 3) M)
    (hmem : (⟨6,M⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L :=
  mountain_classification G O F U E R L M hM hmem

end Paper2.SourceFaithful.HeightThree
