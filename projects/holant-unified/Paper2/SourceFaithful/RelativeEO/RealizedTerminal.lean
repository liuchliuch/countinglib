import Paper2.SourceFaithful.RelativeEO.ARSTerminal
import Paper2.SourceFaithful.RelativeEO.QuaternaryARS
import Paper2.RelativeEO.ARSProductPhase

/-! Canonical fixed-field terminals for actual retained EO gadget outputs.
Each output is first adjoined by its concrete native-X graph and hardness is
transported through that genuine reduction.  The low-arity result is complete;
the arbitrary-arity result below explicitly retains projective ARS. -/
namespace Paper2.SourceFaithful.RelativeEO
open Tractable ExactInput Paper2.RelativeEO

/-- Retaining an actual positive nonzero output preserves exactly the ambient
preprocessing, both supported charge signs, and failure of the K criterion. -/
theorem retained_output (G : Paper1DirectGadgetAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) {n : ℕ} (f : Signature AlgebraicComplex n)
    (hn : 0 < n) (hf : f ≠ 0) (hgraph : NativeNetworkRealizesUpTo L.family f) :
    ∃ N : Language,
      N.family = insert (⟨n,f⟩ : AnySignature AlgebraicComplex) L.family ∧
      L.family ⊆ N.family ∧ Preprocessed N.family ∧ BothChargeSigns N.family ∧
      ¬ Tract (kImage N) ∧ FixedFieldOutput.Reduces .nativeX N L := by
  obtain ⟨N,hN,hNL⟩ := G.adjoin L f hgraph
  have hLN : L.family ⊆ N.family := by rw [hN]; exact Set.subset_insert _ _
  refine ⟨N,hN,hLN,?_,?_,?_,hNL⟩
  · intro g hg
    rw [hN] at hg
    rcases hg with rfl | hg
    · exact ⟨hn,hf⟩
    · exact hpre g hg
  · obtain ⟨⟨g,hg,x,hx,hneg⟩,⟨h,hh,y,hy,hpos⟩⟩ := hboth
    exact ⟨⟨g,hLN hg,x,hx,hneg⟩,⟨h,hLN hh,y,hy,hpos⟩⟩
  · exact fun ht => hnot (ht.mono_family (familyAction_mono sourceKBasis hLN))

/-- A constructed projectively ARS EO output outside the literal B_ARS class
closes the whole original ambient problem at every positive arity. -/
theorem realized_ars_relative_terminal (G : Paper1DirectGadgetAccepted)
    (O : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) {n : ℕ} (f : Signature AlgebraicComplex n)
    (hn : 0 < n) (hf : f ≠ 0) (he : Signature.CentralSupport f)
    (hs : ProjectiveARS f) (hgraph : NativeNetworkRealizesUpTo L.family f)
    (hout : ¬ IsARSProduct f) : FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨N,hN,_,hpreN,hbothN,hnotN,hNL⟩ :=
    retained_output G L hpre hboth hnot f hn hf hgraph
  exact (ars_relative_terminal G O F U E R N hpreN hbothN hnotN f he hs
    (by rw [hN]; exact Set.mem_insert _ _) hout).transport hNL

/-- The complete relative terminal for literal positive EO members of arity at
most four.  Evenness is derived from the actual nonzero central coefficient. -/
theorem low_arity_relative_terminal (G : Paper1DirectGadgetAccepted)
    (O : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (B : Paper1BinaryInterpolationAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) {n : ℕ} (f : Signature AlgebraicComplex n)
    (hn : 0 < n) (hsmall : n ≤ 4) (hf : f ≠ 0)
    (he : Signature.CentralSupport f)
    (hmem : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hout : ¬ IsARSProduct f) : FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨d,hd⟩ := even_arity_of_nonzero_central f hf he
  have hcases : n = 2 ∨ n = 4 := by omega
  rcases hcases with rfl | rfl
  · exact binary_relative_terminal B F U L hpre hboth hnot f hf he hmem hout
  · exact quaternary_relative_terminal G O F U E R B L hpre hboth hnot f hf he hmem hout

/-- Actual low-arity EO gadgets are classified over the original mixed language;
the central output need not have been a literal supplied signature. -/
theorem realized_low_arity_relative_terminal (G : Paper1DirectGadgetAccepted)
    (O : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (B : Paper1BinaryInterpolationAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) {n : ℕ} (f : Signature AlgebraicComplex n)
    (hn : 0 < n) (hsmall : n ≤ 4) (hf : f ≠ 0)
    (he : Signature.CentralSupport f) (hgraph : NativeNetworkRealizesUpTo L.family f)
    (hout : ¬ IsARSProduct f) : FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨N,hN,_,hpreN,hbothN,hnotN,hNL⟩ :=
    retained_output G L hpre hboth hnot f hn hf hgraph
  exact (low_arity_relative_terminal G O F U E R B N hpreN hbothN hnotN f hn hsmall hf he
    (by rw [hN]; exact Set.mem_insert _ _) hout).transport hNL

/-- Contrapositive local classification for the finite low-arity deck. -/
theorem low_arity_realized_isARSProduct (G : Paper1DirectGadgetAccepted)
    (O : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (B : Paper1BinaryInterpolationAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) (hnohard : ¬ FixedFieldOutput.SharpPHard .nativeX L)
    {n : ℕ} (f : Signature AlgebraicComplex n) (hn : 0 < n) (hsmall : n ≤ 4)
    (hf : f ≠ 0) (he : Signature.CentralSupport f)
    (hgraph : NativeNetworkRealizesUpTo L.family f) : IsARSProduct f := by
  by_contra hout
  exact hnohard (realized_low_arity_relative_terminal G O F U E R B L hpre hboth hnot
    f hn hsmall hf he hgraph hout)

/-- The actual EO alternative is complete for binary and quaternary graph
outputs. The nonhard branch keeps an algebraic normalizing scalar. -/
theorem realized_low_arity_eo_alternative (G : Paper1DirectGadgetAccepted)
    (O : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (B : Paper1BinaryInterpolationAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) {n : ℕ} (f : Signature AlgebraicComplex n)
    (hn : 0 < n) (hsmall : n ≤ 4) (hf : f ≠ 0)
    (he : Signature.CentralSupport f) (hgraph : NativeNetworkRealizesUpTo L.family f) :
    ProjectiveARS f ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  by_cases hs : IsARSProduct f
  · exact Or.inl hs.projectiveARS
  · exact Or.inr (realized_low_arity_relative_terminal G O F U E R B L hpre hboth hnot
      f hn hsmall hf he hgraph hs)

end Paper2.SourceFaithful.RelativeEO
