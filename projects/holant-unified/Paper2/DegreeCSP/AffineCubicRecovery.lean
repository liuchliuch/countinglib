import Paper2.DegreeCSP.AffineSupportChart
import Paper2.DegreeCSP.AffineCoordinateSubstitution
import Paper2.DegreeCSP.TernaryBundleGauge

/-! The universal live affine three-face test reconstructs the original
signature. Repeated directions include the unary fourth-power and binary
even-mixed tests. The support chart is proved from literal xor closure and
retains all original coefficients, including all zero and nullary cases. -/
namespace Paper2.DegreeCSP.AffineCubicRecovery
open Tractable
open Holant.Tractable.AffinePhase (Word xor origin)
open Holant.Tractable.TwoTranslate (IsAffineMap)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000

theorem affine_constant_map {r n : ℕ} (a : Word n) : IsAffineMap (fun _ : Word r=>a) := by
  intro x y
  simp

theorem affine_xor {r n : ℕ} (p q : Word r→Word n)
    (hp : IsAffineMap p) (hq : IsAffineMap q) : IsAffineMap (fun x=>xor (p x) (q x)) := by
  intro x y
  change xor (p (xor x y)) (q (xor x y))=_
  rw [hp,hq]
  funext i
  simp only [Holant.Tractable.AffinePhase.xor]
  simp only [Bool.xor_assoc,Bool.xor_left_comm,Bool.xor_comm]

def bitWord {n : ℕ} (b : Bool) (u : Word n) : Word n := if b then u else origin n

theorem affine_bit {r n : ℕ} (j : Fin r) (u : Word n) :
    IsAffineMap (fun x : Word r=>bitWord (x j) u) := by
  intro x y
  change bitWord (Bool.xor (x j) (y j)) u=
    xor (bitWord (x j) u) (xor (bitWord (y j) u) (bitWord false u))
  cases x j <;> cases y j <;> simp [bitWord]

def face {n : ℕ} (a u v w : Word n) (x : Word 3) : Word n :=
  xor (xor (xor a (bitWord (x 0) u)) (bitWord (x 1) v)) (bitWord (x 2) w)

theorem face_affine {n : ℕ} (a u v w : Word n) : IsAffineMap (face a u v w) :=
  affine_xor _ _ (affine_xor _ _
    (affine_xor _ _ (affine_constant_map a) (affine_bit 0 u)) (affine_bit 1 v))
    (affine_bit 2 w)

def cubeTable {n : ℕ} (f : Signature AlgebraicComplex n) (p : Word 3→Word n) :
    TernaryBundleGauge.Table := fun a b c=>f (p ![a,b,c])

theorem face_ratio {n : ℕ} (f : Signature AlgebraicComplex n) (a u v w : Word n) :
    TernaryBundleGauge.cubeRatio (cubeTable f (face a u v w))=
      Holant.Tractable.AffinePhase.thirdRatio f a u v w := by
  simp [TernaryBundleGauge.cubeRatio,cubeTable,face,bitWord,
    Holant.Tractable.AffinePhase.thirdRatio]
  congr 1 <;> ring

theorem affine_of_fullsupport_cubes {n : ℕ} (f : Signature AlgebraicComplex n)
    (live : ∀x,f x≠0)
    (cubes : ∀p : Word 3→Word n,IsAffineMap p→
      TernaryBundleGauge.cubeRatio (cubeTable f p)=1) : Affine f := by
  apply (Paper1Proved.affine_iff _).mpr
  apply Holant.Tractable.AffinePhase.affine_of_thirdTrivial live
  intro a u v w
  rw [←face_ratio]
  exact cubes (face a u v w) (face_affine a u v w)

/-- The final coefficient test on arbitrary supported original affine
three-faces. No live-word decoder or support classifier is supplied. -/
theorem affine_of_live_cubes {n : ℕ} (f : Signature AlgebraicComplex n)
    (hxor : BooleanStructure.Preserves BooleanStructure.xor3 {x | f x≠0})
    (cubes : ∀p : Word 3→Word n,IsAffineMap p→(∀x,f (p x)≠0)→
      TernaryBundleGauge.cubeRatio (cubeTable f p)=1) : Affine f := by
  classical
  by_cases hn : ∃a,f a≠0
  · obtain ⟨a,ha⟩ := hn
    obtain ⟨C⟩ := AffineSupportChart.exists_chart f a ha hxor
    let g : Signature AlgebraicComplex C.rank := fun x=>f (C.map x)
    have hg : Affine g := by
      apply affine_of_fullsupport_cubes g C.live
      intro p hp
      exact cubes (fun x=>C.map (p x))
        (AffineSupportChart.affine_comp p C.map hp C.affine)
        (fun x=>C.live (p x))
    have hs : Affine (fun x=>if f x≠0 then (1 : AlgebraicComplex) else 0) := by
      convert BooleanStructure.affine_indicator_of_xor _ hxor using 1
      funext x
      by_cases hx : f x≠0 <;> simp [BooleanStructure.indicator,hx]
    apply AffineCoordinateSubstitution.reconstruct_live f g hs hg C.coordinate
    intro x hx
    change f (C.map (fun j=>x (C.coordinate j)))=f x
    rw [C.recover x hx]
  · left
    funext x
    exact not_ne_iff.mp (fun hx=>hn ⟨x,hx⟩)

end
end Paper2.DegreeCSP.AffineCubicRecovery
