import Paper2.RelativeEO.BinaryARSDecomposition
import Paper2.RelativeEO.AmbientLifting

/-! Actual finite entry into the EO–ARS prime descent. The input is a literal
ambient member, not a coordinate restriction. The chosen factor and its
algebraic ARS representative are both obtained in retained languages. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
open Paper2.Tractable Paper2.ExactInput Paper2.Problem

/-- Unit rescaling changes only the recorded graph multiplier. -/
theorem nativeRealizes_rescale {F : SignatureFamily AlgebraicComplex} {n : ℕ}
    {f g : Signature AlgebraicComplex n} (hf : NativeNetworkRealizesUpTo F f)
    (c : AlgebraicComplex) (hc : c ≠ 0) (he : f = fun x => c*g x) :
    NativeNetworkRealizesUpTo F g := by
  obtain ⟨N,hN,hX,d,hd,hval⟩ := hf
  refine ⟨N,hN,hX,d*c,mul_ne_zero hd hc,?_⟩
  rw [hval,he]
  funext x
  exact (mul_assoc d c (g x)).symm

/-- Each actual factor block embeds into the original set of ports. -/
theorem decomposition_arity_le {n : ℕ} (D : TensorDecomposition AlgebraicComplex n)
    (i : Fin D.count) : D.arity i ≤ n := by
  have h := Fintype.card_le_of_injective (fun j : Fin (D.arity i) => D.ports ⟨i,j⟩)
    (by intro j k h; exact eq_of_heq (Sigma.mk.inj (D.ports.injective h)).2)
  simpa only [Fintype.card_fin] using h

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
      Reduces .nativeX N L ∧ Reduces .nativeX L N := by
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

end Paper2.RelativeEO
