import Paper2.HeightOne.GroupSplit.PGL
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

/-! Faithful extension of the actual projective quotient to a larger field. -/
namespace Paper2.HeightOne.GroupSplit
open MatrixGroup
noncomputable section
variable {K L : Type*} [Field K] [Field L]

def pglMap (f : K →+* L) : PGL2 K →* PGL2 L :=
  QuotientGroup.map _ _ (Matrix.GeneralLinearGroup.map f) (by
    rintro _ ⟨c, rfl⟩
    exact ⟨(Units.map f) c, (Matrix.GeneralLinearGroup.map_scalar f c).symm⟩)

@[simp] lemma pglMap_mk (f : K →+* L) (U : Matrix.GeneralLinearGroup Bool K) :
    pglMap f (pglMk K U) = pglMk L (Matrix.GeneralLinearGroup.map f U) := rfl

lemma pglMap_injective (f : K →+* L) : Function.Injective (pglMap f) := by
  intro x y
  induction x using Quotient.inductionOn with
  | h U =>
    induction y using Quotient.inductionOn with
    | h V =>
      intro h
      apply pglMk_eq_iff_projectiveClass_eq.mpr
      apply projectiveClass_map_injective f (A := (U : Binary)) (B := (V : Binary))
      · intro hz
        have hd := Matrix.GeneralLinearGroup.det_ne_zero V
        simp [hz] at hd
      · exact pglMk_eq_iff_projectiveClass_eq.mp h

/-- A finite subgroup over algebraic complex numbers is faithfully isomorphic
to its actual complex projective image. No normalization is performed. -/
def subgroupFieldMapEquiv (f : K →+* L) (H : Subgroup (PGL2 K)) :
    H ≃* H.map (pglMap f) :=
  MulEquiv.ofBijective ((pglMap f).subgroupMap H)
    ⟨fun _ _ h => Subtype.ext (pglMap_injective f (congrArg Subtype.val h)),
      by rintro ⟨_, x, hx, rfl⟩; exact ⟨⟨x, hx⟩, rfl⟩⟩

end
end Paper2.HeightOne.GroupSplit
