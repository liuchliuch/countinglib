import Paper2.HeightOne.Dihedral.HighArityMonomial
import Holant.Dihedral.TwoCardLocalization.FusionTags

/-! Finite phase avoidance for the actual negative-root Walsh kernels. The
selected root remains in the original order-N grid; a row-sign identity
transports the already proved trace and fusion choices to M_alpha(-s). -/
namespace Paper2.HeightOne.Dihedral.HighArity
noncomputable section
open Holant Holant.Marked Holant.Dihedral.CompatibleClosure
open Holant.Dihedral.CompatibleCoefficientLine Holant.Dihedral.TwoCardLocalization
set_option backward.isDefEq.respectTransparency false

def rowSign (a : Bool) : Scalar := if a then -1 else 1

theorem rowSign_ne_zero (a : Bool) : rowSign a ≠ 0 := by cases a <;> norm_num [rowSign]

theorem Z_square : Kernel.mul Z Z = Signature.equality := by
  funext a b
  cases a <;> cases b <;> simp [Z,Tractable.diagonalKernel,Kernel.mul_apply,Signature.equality]

theorem parity_Z {α : Bool} {A : Mat} (hA : HasParity α A) :
    HasParity α (Kernel.mul Z A) := by
  obtain ⟨w,hw,rfl⟩ := hA
  refine ⟨fun a => rowSign a * w a,fun a => mul_ne_zero (rowSign_ne_zero a) (hw a),?_⟩
  funext a b
  cases α <;> cases a <;> cases b <;>
    simp [Z,Tractable.diagonalKernel,Kernel.mul_apply,monomial,rowSign]

theorem trace_negative (α : Bool) (A : Mat) (t : Scalar) :
    trace (Kernel.mul Z A) (M α t) = trace A (M α (-t)) := by
  cases α <;> simp [trace,Z,Tractable.diagonalKernel,Kernel.mul_apply,M,monomial] <;> ring

theorem negative_compatible_trace {N : ℕ} (hN : 3 ≤ N) {α : Bool} {A B : Mat}
    (hA : HasParity α A) (hB : HasParity α B) :
    ∃ s : {s : Scalar // Roots N s},
      trace A (M α (-s.val)) ≠ 0 ∧ trace B (M α (-s.val)) ≠ 0 := by
  obtain ⟨s,hsA,hsB⟩ := compatible_trace hN (parity_Z hA) (parity_Z hB)
  exact ⟨s,by simpa only [trace_negative] using hsA,by simpa only [trace_negative] using hsB⟩

theorem negative_fuse {α : Bool} {A : Mat} (hA : HasParity α A) (B : Mat) (t : Scalar) :
    fuse (M false (-t)) A B = scale (rowSign α) (Kernel.mul Z (fuse (M false t) A B)) := by
  obtain ⟨w,hw,rfl⟩ := hA
  funext a b
  cases α <;> cases a <;> cases b <;>
    simp [fuse,Signature.connect,M,monomial,scale,Z,Tractable.diagonalKernel,Kernel.mul_apply,rowSign] <;> ring

theorem negative_absorb_parity_discrepancy {N : ℕ} (hN : 3 ≤ N)
    (α₀ α₁ β : Bool) (A₀ A₁ B₀ B₁ : Mat)
    (hA₀ : HasParity α₀ A₀) (hA₁ : HasParity α₁ A₁)
    (hB₀ : HasParity β B₀) (hB₁ : HasParity (!β) B₁) :
    ∃ s : {s : Scalar // Roots N s},
      ¬ ProjectivelyEqual (fuse (M false (-s.val)) A₁ B₁)
        (fuse (M false (-s.val)) A₀ B₀) := by
  obtain ⟨s,hs⟩ := absorb_parity_discrepancy hN α₀ α₁ β A₀ A₁ B₀ B₁ hA₀ hA₁ hB₀ hB₁
  refine ⟨s,?_⟩
  intro hp
  rw [negative_fuse hA₁ B₁ s.val,negative_fuse hA₀ B₀ s.val] at hp
  have hz := (projective_scale_iff _ _ _ _ (rowSign_ne_zero α₀) (rowSign_ne_zero α₁)).mp hp
  have hh := (ProjectivelyEqual.refl Z).mul hz
  rw [← Kernel.mul_assoc,← Kernel.mul_assoc,Z_square,Kernel.equality_mul,Kernel.equality_mul] at hh
  exact hs hh

end
end Paper2.HeightOne.Dihedral.HighArity
