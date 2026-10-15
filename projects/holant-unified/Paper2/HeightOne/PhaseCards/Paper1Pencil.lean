import Paper2.Paper1Accepted.PhasePencil
import Holant.Projective.CyclicPhasePencil.Algebraic

/-! The exact Paper 1 pencil theorem, instantiated from its frozen,
kernel-checked algebraic proof. This discharges the pure accepted interface;
no Paper 2 classification statement is assumed. -/
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable PhasePencil

lemma safe_iff_paper1_scalarSamples {N : ℕ} (hN : 0 < N)
    (a b c d : AlgebraicComplex) :
    Safe N a b c d ↔
      Holant.Projective.CyclicPhasePencil.ScalarSamples N a b c d := by
  constructor
  · intro h s hs
    rcases h s hs with ⟨hu, hv⟩ | ⟨η, κ, hη, hκ, hu, hv⟩
    · exact Or.inl ⟨hu, by linear_combination -hv⟩
    · have hη0 : η ≠ 0 :=
        Holant.Projective.CyclicPhasePencil.root_ne_zero hN hη
      have he : -c + s * d = κ * η := by linear_combination -hv
      exact Or.inr ⟨by simpa [hu] using hκ,
        by simpa [he] using mul_ne_zero hκ hη0,
        by simpa [he, hu, hκ, Root] using hη⟩
  · intro h s hs
    rcases h s hs with ⟨hu, hv⟩ | ⟨hu, hv, hroot⟩
    · exact Or.inl ⟨hu, by linear_combination -hv⟩
    · refine Or.inr ⟨(-c + s * d) / (a - s * b), a - s * b,
        hroot, hu, rfl, ?_⟩
      field_simp
      ring

/-- An actual value of the pure Paper 1 interface, supplied by the existing
Paper 1 Lean proof with the displayed matrix-sign convention checked. -/
theorem provedPhasePencil : Paper1PhasePencilAccepted where
  phasePencil_7_1 N hN a b c d := by
    have h := Holant.Projective.CyclicPhasePencil.cyclic_phase_pencil_algebraic
      hN a b c d
    change PhasePencil.Relation N a b c d ↔
      Holant.Projective.CyclicPhasePencil.MatrixSamples N a b c d at h
    rw [Holant.Projective.CyclicPhasePencil.matrixSamples_iff (by omega)] at h
    exact h.trans (safe_iff_paper1_scalarSamples (by omega) a b c d).symm

end
end Paper2.HeightOne.PhaseCards

