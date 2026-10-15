import Paper2.HeightOne.Dihedral.HighArityTagsSix
import Paper2.HeightOne.Dihedral.HighArityFactorization
import Holant.Dihedral.CompatibleCoefficientLine.MatchingAgreement
import Holant.Dihedral.SectorRuling.SampleSelection

/-! The complete signed high-arity analytic deck. Matching and coefficient
line agreement are derived by the two independent localization theorems;
four-card inversion then exhibits a genuine proper cut of the ancestor. -/
namespace Paper2.HeightOne.Dihedral.HighArity
noncomputable section
open Holant Holant.Marked Holant.Certificates
open Holant.Certificates.MatchingContractionClosure
open Holant.Dihedral.CompatibleClosure
open Holant.Dihedral.CompatibleCoefficientLine
open Holant.Dihedral.TwoCardLocalization (DifferentProducts presentationMatching)
open Holant.Dihedral.EndpointParallelogram (Pairing)
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000

private theorem matching_fixed_count {r : ℕ} (g : Signature Scalar (2*r+4))
    (hg : MatchingOrZero monomialGroup g) (hn : g ≠ 0) :
    ∃ p : (Fin (r+2) × Bool) ≃ Fin (2*r+4),∃ A : Fin (r+2) → Mat,∃ κ : Scalar,
      (∀ e,IsMonomial (A e)) ∧ κ ≠ 0 ∧ g = Holant.Dihedral.CompatibleClosure.productValue p A κ := by
  obtain ⟨M,hM,hκ,he⟩ := hg.resolve_left hn
  have hc := Fintype.card_congr M.ports
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hc
  have hcount : M.edges = r+2 := by omega
  cases M with
  | mk count p A κ =>
    dsimp only at hcount
    subst count
    exact ⟨p,A,κ,fun e => (safe_monomial_iff _).mp (hM e),hκ,he⟩

private theorem align_matching {n k : ℕ} (p₀ p₁ : (Fin k × Bool) ≃ Fin n)
    (hm : ∀ u,(Pairing.ofPorts p₀).mate u = (Pairing.ofPorts p₁).mate u)
    (A : Fin k → Mat) (hA : ∀ e,IsMonomial (A e)) (κ : Scalar) :
    ∃ B : Fin k → Mat,(∀ e,IsMonomial (B e)) ∧
      Holant.Dihedral.CompatibleClosure.productValue p₀ B κ =
        Holant.Dihedral.CompatibleClosure.productValue p₁ A κ := by
  cases k with
  | zero =>
    refine ⟨A,hA,?_⟩
    funext x
    simp [Holant.Dihedral.CompatibleClosure.productValue]
  | succ k =>
    have hc := Fintype.card_congr p₀
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hc
    have hn : n = 2*k+2 := by omega
    clear hc
    subst n
    let L := MatchingAlignment.ofMate p₀ p₁ hm
    refine ⟨L.factors A,?_,L.product_eq A κ⟩
    intro e
    unfold MatchingAlignment.factors
    split
    · exact (hA _).transpose
    · exact hA _

/-- All actual order-N signed kernels, in every original port order, force a
proper tensor factor at arity at least eight. No additional matching, phase,
support, coefficient or factorization premise is supplied. -/
theorem signed_deck_not_tensorPrime {N : ℕ} (hN : 3 ≤ N)
    (r : ℕ) (hr : 1 ≤ r) (q : Paper2.Signature Scalar (2*r+6))
    (hcards : ∀ i : PhaseLabel N,∀ p : Equiv.Perm (Fin (2*r+6)),
      MatchingOrZero monomialGroup
        (Holant.Signature.contract (phaseKernel i) (Holant.Tensor.reindex p.symm q))) :
    ¬ Paper2.TensorPrime q := by
  classical
  obtain ⟨t,ht,ht1,_⟩ := Holant.Dihedral.SectorRuling.third_root hN 1 1 (Roots.one N) (Roots.one N)
  have ht0 : t ≠ 0 := ht.ne_zero (by omega)
  let labels : Sample → PhaseLabel N := fun i =>
    (i.1,if i.2 then ⟨t,ht⟩ else ⟨1,Roots.one N⟩)
  have hlabel (i : Sample) : phaseKernel (labels i) = M i.1 (phase (-1) (-t) i) := by
    rcases i with ⟨a,b⟩
    cases b <;> rfl
  have hmono (i : Sample) : IsMonomial (M i.1 (phase (-1) (-t) i)) := by
    rw [← hlabel]
    exact phaseKernel_monomial (by omega) _
  have hclose (i : Sample) : MatchingOrZero monomialGroup (close i.1 (phase (-1) (-t) i) q) := by
    have h := hcards (labels i) (Equiv.refl _)
    have hc : close i.1 (phase (-1) (-t) i) q =
        Holant.Signature.contract (M i.1 (phase (-1) (-t) i)) q := rfl
    rw [hc]
    simpa only [hlabel,Equiv.refl_symm,Holant.Tensor.reindex_refl] using h
  have hphase : (-1 : Scalar) ≠ -t := by
    intro h
    exact ht1 (neg_injective h).symm
  intro hprime
  have hn : ∃ i : Sample,close i.1 (phase (-1) (-t) i) q ≠ 0 := by
    by_contra hz
    push Not at hz
    have H := four_card_inversion (-1) (-t) hphase q (0 : Mat) (fun _ => 0) (by
      intro i a b x
      rw [hz i]
      simp)
    apply hprime.1
    funext x
    have hh := H (x 0) (x 1) (tail x 0) (tail x 1) (tail (tail x))
    rw [pair_eta,pair_eta] at hh
    simpa using hh
  let I := {i : Sample // close i.1 (phase (-1) (-t) i) q ≠ 0}
  have H (i : I) := matching_fixed_count _ (hclose i.val) i.property
  choose p A κ hA hκ he using H
  obtain ⟨i₀,hi₀⟩ := hn
  let j₀ : I := ⟨i₀,hi₀⟩
  let baseline := p j₀
  have hmate (i : I) : ∀ u,(Pairing.ofPorts baseline).mate u = (Pairing.ofPorts (p i)).mate u := by
    let M₀ : Presentation Scalar (Fin (2*r+4)) := ⟨r+2,p j₀,A j₀,κ j₀⟩
    let M₁ : Presentation Scalar (Fin (2*r+4)) := ⟨r+2,p i,A i,κ i⟩
    have hm : (presentationMatching M₀).mate = (presentationMatching M₁).mate := by
      by_contra hbad
      let C : Mat := M false (-1)
      have hC : IsMonomial C := M_isMonomial false (by norm_num)
      have hfixed : ∀ o : Equiv.Perm (Fin (2*r+6)),MatchingOrZero monomialGroup
          (Holant.Signature.contract C (Holant.Tensor.reindex o.symm q)) := by
        intro o
        exact hcards (false,⟨1,Roots.one N⟩) o
      apply no_different_matching_cards r hr q C hC hfixed
        (M j₀.val.1 (phase (-1) (-t) j₀.val)) (M i.val.1 (phase (-1) (-t) i.val))
        (hmono j₀.val) (hmono i.val)
      exact ⟨M₀,M₁,fun e => (safe_monomial_iff _).mpr (hA j₀ e),
        fun e => (safe_monomial_iff _).mpr (hA i e),hκ j₀,hκ i,he j₀,he i,hbad⟩
    intro u
    exact congrArg (fun z => z u) hm
  have halign (i : I) := align_matching baseline (p i) (hmate i) (A i) (hA i) (κ i)
  choose B hB hBprod using halign
  have hEq (i : I) : close i.val.1 (phase (-1) (-t) i.val) q =
      Holant.Dihedral.CompatibleClosure.productValue baseline (B i) (κ i) :=
    (he i).trans (hBprod i).symm
  have hp (i j : I) (e f : Fin (r+2)) (hef : e ≠ f) :
      ProjectivelyEqual (B i e) (B j e) ∨ ProjectivelyEqual (B i f) (B j f) := by
    by_contra h
    push Not at h
    apply no_two_tags_matching_cards hN r hr q hcards
      (M j.val.1 (phase (-1) (-t) j.val)) (M i.val.1 (phase (-1) (-t) i.val))
      (hmono j.val) (hmono i.val)
    exact ⟨r+2,baseline,B j,B i,κ j,κ i,hB j,hB i,hκ j,hκ i,hEq j,hEq i,e,f,hef,h.1,h.2⟩
  exact four_cards_not_tensorPrime (by omega : 2 ≤ r+2) q (-1) (-t) hphase
    baseline B κ hEq hp hprime

end
end Paper2.HeightOne.Dihedral.HighArity

