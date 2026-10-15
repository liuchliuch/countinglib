import Paper2.SourceFaithful.SourceStatements.PhaseProductParityCyclic

/-! Actual representative scalars in source Lemma 5.12. No representative
is normalized away: multiplying a complete card by any nonzero coefficient
preserves the literal zero-or-nonsingular cyclic condition. -/
namespace Paper2.SourceFaithful.SourceStatements.PhaseProductParity
noncomputable section
open Tractable PhasePencil HeightOne HeightOne.Dihedral HeightOne.PhaseCards

def ScaledCyclicContractions (N : ℕ)
    (c : Fin 4 → Fin 4 → AlgebraicComplex → AlgebraicComplex)
    (f : Signature AlgebraicComplex 4) : Prop :=
  ∀ (i j : Fin 4) (hij : i ≠ j) (s : AlgebraicComplex), Root N s →
    SupportedOnParity (c i j s • plusContraction i j hij s f) 0 ∧
      ∀ x, RootComplement N ((c i j s • plusContraction i j hij s f) x)
        ((c i j s • plusContraction i j hij s f) (fun k => !(x k)))

theorem scaled_cyclic_iff {N : ℕ}
    (c : Fin 4 → Fin 4 → AlgebraicComplex → AlgebraicComplex)
    (hc : ∀ i j s, Root N s → c i j s ≠ 0) (f : Signature AlgebraicComplex 4) :
    ScaledCyclicContractions N c f ↔ CyclicContractions N f := by
  constructor
  · intro h i j hij s hs
    refine ⟨(supportedOnParity_scale_iff _ (hc i j s hs) _ _).mp (h i j hij s hs).1,?_⟩
    intro x
    exact (RootComplement.smul_iff _ _ _ (hc i j s hs)).mp ((h i j hij s hs).2 x)
  · intro h i j hij s hs
    refine ⟨(supportedOnParity_scale_iff _ (hc i j s hs) _ _).mpr (h i j hij s hs).1,?_⟩
    intro x
    exact (RootComplement.smul_iff _ _ _ (hc i j s hs)).mpr ((h i j hij s hs).2 x)

theorem source_5_12_scaled {N : ℕ} (hN : 3 ≤ N)
    (c : Fin 4 → Fin 4 → AlgebraicComplex → AlgebraicComplex)
    (hc : ∀ i j s, Root N s → c i j s ≠ 0)
    (f : Signature AlgebraicComplex 4) (heven : SupportedOnParity f 0) :
    ScaledCyclicContractions N c f ↔
      CyclicNormalForm N (f (fun _ => false)) (f (fun _ => true))
        (fun i => f (centralWord i (fun _ => false)))
        (fun i => f (flipAll (centralWord i (fun _ => false)))) :=
  (scaled_cyclic_iff c hc f).trans (source_5_12 hN f heven)

end
end Paper2.SourceFaithful.SourceStatements.PhaseProductParity
