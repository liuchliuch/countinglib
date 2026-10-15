import Paper2.DegreeCSP.GeneratedCodeSeven
import Paper2.DegreeCSP.GeneratedAffineSubstitution

/-! A genuine Hadamard anchor produces the seven-character support mask.
Three anchor copies and one hidden sum give a scaled XOR gate. Four actual
pulled-back gates enforce the code, retaining their complete scalar. -/
namespace Paper2.DegreeCSP.GeneratedCodeSevenFromAnchor
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

def scalar (a : AlgebraicComplex) : AlgebraicComplex := (2*a^3)^4

theorem scalar_ne_zero {a : AlgebraicComplex} (ha : a≠0) : scalar a≠0 :=
  pow_ne_zero _ (GeneratedAffineSubstitution.parity_scale_ne_zero ha)

theorem generated {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    {a : AlgebraicComplex} (hanchor : Generated F k (GeneratedHadamardUnary.anchor a)) :
    Generated F k (fun y : Fin 7→Bool=>scalar a*GeneratedCodeSeven.indicator y) := by
  have hp : Generated F k (GeneratedCodeSeven.scaledParity (2*a^3) false) := by
    convert GeneratedAffineSubstitution.parity_generated hanchor using 1
    funext x
    by_cases h:x 2=Bool.xor (x 0) (x 1) <;>
      simp [GeneratedCodeSeven.scaledParity,GeneratedAffineSubstitution.parity,h]
  exact GeneratedCodeSeven.generated_code (2*a^3) hp

/-- No generated decoder or support mask is supplied by the caller. The
nonzero mask scalar is the literal contribution of twelve anchor copies. -/
theorem exists_scaled_code {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (a : AlgebraicComplex) (ha : a≠0)
    (hanchor : Generated F k (GeneratedHadamardUnary.anchor a)) :
    ∃c : AlgebraicComplex,c≠0 ∧
      Generated F k (fun y : Fin 7→Bool=>c*GeneratedCodeSeven.indicator y) :=
  ⟨scalar a,scalar_ne_zero ha,generated hanchor⟩

end
end Paper2.DegreeCSP.GeneratedCodeSevenFromAnchor
