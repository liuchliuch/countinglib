import Paper2.SourceFaithful.RelativeEO.QuaternaryTerminal
import Paper2.SourceFaithful.RelativeEO.PrimeEntry
import Paper2.RelativeEO.GramNonmatching

/-! Full ambient projective-ARS relative EO terminal in canonical fixed-field
output semantics. The proof uses a new explicit two-copy Gram construction,
not the wholly EO–ARS-language theorem and not an assumed CFS descent. -/
namespace Paper2.SourceFaithful.RelativeEO
open Tractable ExactInput Paper2.RelativeEO

/-- A literal nonbinary prime exact EO–ARS member yields an actual nonmatching
quaternary graph, and hence hardness of the whole mixed ambient language. -/
theorem prime_ARS_terminal (G : Paper1DirectGadgetAccepted)
    (O : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) {n : ℕ} (f : Signature AlgebraicComplex n)
    (hn : 4 ≤ n) (hp : TensorPrime f) (he : Signature.CentralSupport f) (hs : ARS f)
    (hmem : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨i,j,hij,hg,hge,hgout⟩ := prime_ARS_nonmatching_mating f hn hp he hs
  obtain ⟨N,hN,hNL⟩ := G.adjoin L (gramTable i j hij f) (gramTable_realized i j hij f hmem)
  have hLN : L.family ⊆ N.family := by rw [hN]; exact Set.subset_insert _ _
  have hpreN : Preprocessed N.family := by
    intro g hgm
    rw [hN] at hgm
    rcases hgm with rfl | hgm
    · exact ⟨by change 0 < (4 : ℕ); decide,hg⟩
    · exact hpre g hgm
  have hbothN : BothChargeSigns N.family := by
    obtain ⟨⟨f,hf,x,hx,hn⟩,⟨g,hg,y,hy,hp⟩⟩ := hboth
    exact ⟨⟨f,hLN hf,x,hx,hn⟩,⟨g,hLN hg,y,hy,hp⟩⟩
  have hnotN : ¬ Tract (kImage N) := fun ht =>
    hnot (ht.mono_family (familyAction_mono sourceKBasis hLN))
  exact (quaternary_nonmatching_terminal G O F U E R N hpreN hbothN hnotN
    (gramTable i j hij f) hg hge (by rw [hN]; exact Set.mem_insert _ _) hgout).transport hNL

/-- Paper 2 Lemma 3.10 in full positive arity, for the actual original finite
language. All algebraic prime factors and their exact ARS rescalings are adjoined
through genuine retained reductions; the two-copy output is a native-X graph. -/
theorem ars_relative_terminal (G : Paper1DirectGadgetAccepted)
    (O : Paper1OccurrenceAccepted) (F : Paper1FactorClosureAccepted)
    (U : Paper1UnaryAccepted) (E : Paper1EOAccepted) (R : Paper1RestrictionAccepted)
    (L : Language) (hpre : Preprocessed L.family) (hboth : BothChargeSigns L.family)
    (hnot : ¬ Tract (kImage L)) {n : ℕ} (f : Signature AlgebraicComplex n)
    (he : Signature.CentralSupport f) (hs : ProjectiveARS f)
    (hmem : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hout : ¬ IsARSProduct f) : FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨m,g,N,hm,_,_,hgp,hge,hgs,hgm,hLN,hpreN,hNL,_⟩ :=
    prime_eoARS_entry G F R L hpre (bothChargeSigns_not_oneSided hboth) f hmem he hs hout
  have hbothN : BothChargeSigns N.family := by
    obtain ⟨⟨f,hf,x,hx,hn⟩,⟨g,hg,y,hy,hp⟩⟩ := hboth
    exact ⟨⟨f,hLN hf,x,hx,hn⟩,⟨g,hLN hg,y,hy,hp⟩⟩
  have hnotN : ¬ Tract (kImage N) := fun ht =>
    hnot (ht.mono_family (familyAction_mono sourceKBasis hLN))
  exact (prime_ARS_terminal G O F U E R N hpreN hbothN hnotN g hm hgp hge hgs hgm).transport hNL

end Paper2.SourceFaithful.RelativeEO
