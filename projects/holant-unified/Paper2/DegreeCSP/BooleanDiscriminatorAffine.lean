import Paper2.DegreeCSP.BooleanSupport

/-! Discriminator-preserved Boolean relations are also xor-preserved. Binary
projections supply the literal finite support cases; majority reconstruction
then assembles the actual relation, including empty and nullary supports. -/
namespace Paper2.DegreeCSP.BooleanStructure
open Tractable
noncomputable section
set_option maxHeartbeats 800000

/-- The actual sixteen Boolean binary support tables leave only cases that
also preserve xor; the three-corner tables violate discriminator preservation. -/
theorem binary_xor_of_discriminator (B : Bool→Bool→Prop)
    (hB : PreservesBinary discriminator B) : PreservesBinary xor3 B := by
  classical
  by_cases h00 : B false false <;> by_cases h01 : B false true <;>
    by_cases h10 : B true false <;> by_cases h11 : B true true
  all_goals simp_all [PreservesBinary,discriminator,xor3,Bool.forall_bool]

/-- Pairwise reconstruction transfers the xor-preserved binary projections
back to the original finite Boolean relation. -/
theorem preserves_xor_of_discriminator {n : ℕ} (R : Set (Fin n→Bool))
    (hR : Preserves discriminator R) : Preserves xor3 R := by
  classical
  intro x hx y hy z hz
  apply pairwise_reconstruct R ⟨x,hx⟩ (preserves_majority hR)
  intro i j
  have hp := binary_xor_of_discriminator (projection R i j)
    (projection_preserves discriminator R hR i j)
  exact hp (x i) (x j) (y i) (y j) (z i) (z j)
    ⟨x,hx,rfl,rfl⟩ ⟨y,hy,rfl,rfl⟩ ⟨z,hz,rfl,rfl⟩

/-- The support indicator has an actual affine-system presentation. This
classifies the indicator and makes no assertion about arbitrary coefficients. -/
theorem affine_indicator_of_discriminator {n : ℕ} (R : Set (Fin n→Bool))
    (hR : Preserves discriminator R) : Affine (indicator R) :=
  affine_indicator_of_xor R (preserves_xor_of_discriminator R hR)

end
end Paper2.DegreeCSP.BooleanStructure
