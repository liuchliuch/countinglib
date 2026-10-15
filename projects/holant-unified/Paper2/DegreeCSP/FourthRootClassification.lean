import Paper2.Tractable.Affine

/-! Literal fourth roots in the algebraic-complex field and their residue phases. -/
namespace Paper2.DegreeCSP.FourthRootClassification
open Tractable
noncomputable section

private theorem imaginaryUnit_pow_mod_four (n : ℕ) :
    imaginaryUnit ^ (n % 4) = imaginaryUnit ^ n := by
  symm
  calc
    imaginaryUnit ^ n = imaginaryUnit ^ (n % 4 + 4 * (n / 4)) :=
      congrArg (fun k => imaginaryUnit ^ k) (Nat.mod_add_div n 4).symm
    _ = imaginaryUnit ^ (n % 4) := by
      rw [pow_add,pow_mul,imaginaryUnit_pow_four,one_pow,mul_one]

/-- Residue addition is literal multiplication of the corresponding phases. -/
theorem phase_add (q r : ZMod 4) :
    fourthRootPhase (q+r) = fourthRootPhase q * fourthRootPhase r := by
  simp only [fourthRootPhase,ZMod.val_add,imaginaryUnit_pow_mod_four,pow_add]

/-- Factorization in the actual field leaves exactly four possible roots. -/
theorem root_cases {u : AlgebraicComplex} (hu : u^4=1) :
    u=1 ∨ u=imaginaryUnit ∨ u= -1 ∨ u= -imaginaryUnit := by
  have hf : (u-1)*(u+1)*(u-imaginaryUnit)*(u+imaginaryUnit) = u^4-1 := by
    calc
      _ = (u^2-1)*(u^2-imaginaryUnit^2) := by ring
      _ = _ := by rw [imaginaryUnit_sq]; ring
  have hz : (u-1)*(u+1)*(u-imaginaryUnit)*(u+imaginaryUnit)=0 := by
    rw [hf,hu,sub_self]
  rcases mul_eq_zero.mp hz with h | h
  · rcases mul_eq_zero.mp h with h | h
    · rcases mul_eq_zero.mp h with h | h
      · exact Or.inl (sub_eq_zero.mp h)
      · exact Or.inr (Or.inr (Or.inl (by linear_combination h)))
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
  · exact Or.inr (Or.inr (Or.inr (by linear_combination h)))

/-- Every literal fourth root has a `ZMod 4` phase representative. -/
theorem exists_phase {u : AlgebraicComplex} (hu : u^4=1) :
    ∃ q : ZMod 4,fourthRootPhase q=u := by
  rcases root_cases hu with h | h | h | h
  · exact ⟨0,by simpa using h.symm⟩
  · refine ⟨1,?_⟩
    change imaginaryUnit^1=u
    simpa using h.symm
  · refine ⟨2,?_⟩
    change imaginaryUnit^2=u
    rw [imaginaryUnit_sq]
    exact h.symm
  · refine ⟨3,?_⟩
    change imaginaryUnit^3=u
    calc
      imaginaryUnit^3 = imaginaryUnit^2*imaginaryUnit := by ring
      _ = -imaginaryUnit := by rw [imaginaryUnit_sq]; ring
      _ = u := h.symm

end
end Paper2.DegreeCSP.FourthRootClassification
