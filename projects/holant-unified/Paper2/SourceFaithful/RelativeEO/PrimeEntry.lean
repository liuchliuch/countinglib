import Paper2.SourceFaithful.FactorClosure
import Paper2.SourceFaithful.GadgetAugmentation
import Paper2.RelativeEO.PrimeEntry

/-! Actual EO–ARS prime entry in canonical fixed-field output semantics. All
ordered factorization and normalization proofs are reused as pure mathematics;
the two genuine reductions are reconstructed from source-faithful inputs. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.SourceFaithful.RelativeEO
open Tractable ExactInput Paper2.RelativeEO

/-- This is the actual algebraic prime-entry portion of Paper 2 Lemma 3.10.
No subsequent CFS descent or ambient hardness statement is assumed here. -/
theorem prime_eoARS_entry (G : Paper1DirectGadgetAccepted)
    (F : Paper1FactorClosureAccepted) (R : Paper1RestrictionAccepted)
    (L : Language) (hpre : Preprocessed L.family) (htwo : ¬ CommonOneSided L.family)
    {n : ℕ} (h : Signature AlgebraicComplex n)
    (hmem : (⟨n,h⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (he : Signature.CentralSupport h) (hs : ProjectiveARS h) (hout : ¬ IsARSProduct h) :
    ∃ (m : ℕ) (f : Signature AlgebraicComplex m) (N : Language),
      4 ≤ m ∧ m ≤ n ∧ (∃ d, m = 2*d) ∧ TensorPrime f ∧
      Signature.CentralSupport f ∧ ARS f ∧
      (⟨m,f⟩ : AnySignature AlgebraicComplex) ∈ N.family ∧
      L.family ⊆ N.family ∧ Preprocessed N.family ∧
      FixedFieldOutput.Reduces .nativeX N L ∧ FixedFieldOutput.Reduces .nativeX L N := by
  classical
  have hnonzero := (hpre _ hmem).2
  obtain ⟨D,hD,hpos,hprime,hcentral,hars⟩ :=
    exists_prime_eoARS_decomposition h (hpre _ hmem).1 hnonzero he hs
  have hex : ∃ i, D.arity i ≠ 2 := by
    by_contra hh
    push Not at hh
    exact hout (hD ▸ binary_decomposition_isARSProduct D hh (fun i => (hprime i).1) hcentral hars)
  obtain ⟨i,hi⟩ := hex
  obtain ⟨d,hd⟩ := even_arity_of_nonzero_central (D.factor i) (hprime i).1 (hcentral i)
  have hfour : 4 ≤ D.arity i := by have hp := hpos i; omega
  obtain ⟨M,hLM,hfactors,hpreM,_,hML,_⟩ := factorClosure_with_member_decomposition
    F L hpre htwo h hmem D hD hpos hprime
  obtain ⟨c,f,hc,hfactor,hpf,hef,hsf⟩ := exact_ARS_representative
    (D.factor i) (hprime i) (hcentral i) (hars i)
  have hgraph : NativeNetworkRealizesUpTo M.family f :=
    nativeRealizes_rescale (NativeNetworkRealizesUpTo.of_mem (hfactors i)) c hc hfactor
  obtain ⟨N,hN,hNM⟩ := G.adjoin M f hgraph
  have hMN : M.family ⊆ N.family := by rw [hN]; exact Set.subset_insert _ _
  have hLN := hLM.trans hMN
  refine ⟨D.arity i,f,N,hfour,decomposition_arity_le D i,⟨d,hd⟩,hpf,hef,hsf,?_,hLN,?_,
    hNM.trans hML,R.restriction_2_5 L N hLN⟩
  · rw [hN]
    exact Set.mem_insert _ _
  · intro g hg
    rw [hN] at hg
    rcases hg with rfl | hg
    · exact ⟨by change 0 < D.arity i; omega,hpf.1⟩
    · exact hpreM g hg


end Paper2.SourceFaithful.RelativeEO
