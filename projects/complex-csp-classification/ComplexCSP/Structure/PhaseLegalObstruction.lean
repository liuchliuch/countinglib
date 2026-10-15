import ComplexCSP.Structure.PhaseSupportObstruction
import ComplexCSP.Algebra.PurePowerExponent

/-! # Both obstruction branches for actual legal purifications

The phase exponent and positive normalization come from the constructed legal
purification. They are not extra supplied hypotheses of the obstruction theorem.
-/
namespace ComplexCSP.PhaseLegalObstruction
open BlockOrthogonality PhasePowerAlgebra GeneratingSet
variable {X D : Type} [Fintype X] [Fintype D]

theorem pure_obstruction (G : X → D → ℂ) (hpure : ∀ x z,IsPureValue (G x z))
    (hBO : ¬BlockOrthogonal G) :
    ∃ K : ℕ, 2≤K ∧ 2∣K ∧ (¬BlockRankOne G ∨
      ∃ t : ℕ, 0<t ∧ t≤Fintype.card D ∧
        ¬BlockRankOne (fun x y => powerPair (G x) (G y) (t*K))) := by
  classical
  obtain ⟨K,hK,heven,hpow⟩ := PurePowerExponent.exists_power_norm
    (fun p : X × D => G p.1 p.2) (fun p => hpure p.1 p.2)
  refine ⟨K,hK,heven,?_⟩
  by_cases hr : BlockRankOne G
  · exact Or.inr (PhaseSupportObstruction.matrix_obstruction G hr hBO K (by omega)
      (fun x z => hpow (x,z)))
  · exact Or.inl hr

/-- Exact dichotomy of obstructions after actual legal normalization. This is
finite algebra, not the external #P-hardness conclusion. -/
theorem legal_obstruction {S : Finset ℂˣ} (L : LegalGeneratingSet S)
    (G : X → D → ℂ) (hG : LegalGeneratingSet.ContainsTable S G)
    (hBO : ¬BlockOrthogonal (L.purifyTable G hG)) :
    ∃ s K : ℕ, 0<s ∧ 2≤K ∧ 2∣K ∧
      (¬BlockRankOne (fun x z => (s : ℂ)*L.purifyTable G hG x z) ∨
        ∃ t : ℕ, 0<t ∧ t≤Fintype.card D ∧
          ¬BlockRankOne (fun x y => powerPair
            (fun z => (s : ℂ)*L.purifyTable G hG x z)
            (fun z => (s : ℂ)*L.purifyTable G hG y z) (t*K))) := by
  obtain ⟨s,hs,hpure⟩ := L.table_exists_pure_normalization G hG
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hs
  have hnot : ¬BlockOrthogonal (fun x z => (s : ℂ)*L.purifyTable G hG x z) := by
    intro hh
    exact hBO ((blockOrthogonal_scale_iff hs0 (L.purifyTable G hG)).mp hh)
  obtain ⟨K,hK,heven,ho⟩ := pure_obstruction _ hpure hnot
  exact ⟨s,K,hs,hK,heven,ho⟩

/-- The normalized-table scaling is not needed in the oracle problem: it
cancels from the common phase exponent identity, giving both branches directly
for the actual unscaled legal purification. -/
theorem legal_unscaled_obstruction {S : Finset ℂˣ} (L : LegalGeneratingSet S)
    (G : X → D → ℂ) (hG : LegalGeneratingSet.ContainsTable S G)
    (hBO : ¬BlockOrthogonal (L.purifyTable G hG)) :
    ∃ K : ℕ, 2≤K ∧ 2∣K ∧
      (¬BlockRankOne (L.purifyTable G hG) ∨
        ∃ t : ℕ, 0<t ∧ t≤Fintype.card D ∧
          ¬BlockRankOne (fun x y => powerPair
            (L.purifyTable G hG x) (L.purifyTable G hG y) (t*K))) := by
  classical
  obtain ⟨K,hK,heven,hpow⟩ := PurePowerExponent.exists_legal_power_norm_unscaled L G hG
  refine ⟨K,hK,heven,?_⟩
  by_cases hr : BlockRankOne (L.purifyTable G hG)
  · exact Or.inr (PhaseSupportObstruction.matrix_obstruction _ hr hBO K (by omega) hpow)
  · exact Or.inl hr

end ComplexCSP.PhaseLegalObstruction
