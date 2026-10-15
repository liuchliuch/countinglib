import Paper2.DegreeCSP.AffineLiveCoordinates

/-! The literal live-coordinate bijection on an affine support has a genuine
affine inverse. Its coefficients are never changed: the chart only selects
actual supported words of the supplied signature. -/
namespace Paper2.DegreeCSP.AffineSupportChart
open Tractable
open GeneratedCoordinateMarginal (Live liveProjection)
open Holant.Tractable.AffinePhase (Word xor origin)
open Holant.Tractable.TwoTranslate (IsAffineMap)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {n : ℕ}

structure Chart (f : Signature AlgebraicComplex n) where
  rank : ℕ
  coordinate : Fin rank→Fin n
  map : Word rank→Word n
  live : ∀x,f (map x)≠0
  selected : ∀x j,map x (coordinate j)=x j
  recover : ∀x,f x≠0→map (fun j=>x (coordinate j))=x
  affine : IsAffineMap map

def ofProjection (f : Signature AlgebraicComplex n) {r : ℕ} (q : Fin r→Fin n)
    (hbij : Function.Bijective (liveProjection f q))
    (hxor : BooleanStructure.Preserves BooleanStructure.xor3 {x | f x≠0}) : Chart f := by
  let e := Equiv.ofBijective (liveProjection f q) hbij
  let p : Word r→Word n := fun x=>(e.symm x).val
  have live (x : Word r) : f (p x)≠0 := (e.symm x).property
  have selected (x : Word r) (j : Fin r) : p x (q j)=x j :=
    congrFun (e.apply_symm_apply x) j
  have recover (x : Word n) (hx : f x≠0) : p (fun j=>x (q j))=x :=
    congrArg Subtype.val (e.symm_apply_apply ⟨x,hx⟩)
  have affine : IsAffineMap p := by
    intro x y
    let w := xor (xor (p x) (p y)) (p (origin r))
    have hw : f w≠0 := hxor _ (live x) _ (live y) _ (live (origin r))
    have he : e ⟨p (xor x y),live (xor x y)⟩=e ⟨w,hw⟩ := by
      funext j
      change p (xor x y) (q j)=w (q j)
      simp only [selected,w,Holant.Tractable.AffinePhase.xor,
        Holant.Tractable.AffinePhase.origin,Bool.xor_false]
    simpa only [w,Holant.Tractable.AffinePhase.xor_assoc] using
      congrArg Subtype.val (e.injective he)
  exact ⟨r,q,p,live,selected,recover,affine⟩

theorem exists_chart (f : Signature AlgebraicComplex n)
    (a : Word n) (ha : f a≠0)
    (hxor : BooleanStructure.Preserves BooleanStructure.xor3 {x | f x≠0}) :
    Nonempty (Chart f) := by
  obtain ⟨r,q,_hq,hbij⟩ := AffineLiveCoordinates.exists_live_coordinates_xor f a ha hxor
  exact ⟨ofProjection f q hbij hxor⟩

/-- Affine maps preserve the three-word parity operation without an origin
correction. This also proves composition for different finite dimensions. -/
theorem affine_triple {r m : ℕ} (p : Word r→Word m) (hp : IsAffineMap p)
    (x y z : Word r) : p (xor (xor x y) z)=xor (xor (p x) (p y)) (p z) := by
  rw [hp,hp]
  funext i
  simp only [Holant.Tractable.AffinePhase.xor]
  cases p x i <;> cases p y i <;> cases p z i <;> cases p (origin r) i <;> rfl

theorem affine_comp {r m l : ℕ} (p : Word r→Word m) (q : Word m→Word l)
    (hp : IsAffineMap p) (hq : IsAffineMap q) : IsAffineMap (fun x=>q (p x)) := by
  intro x y
  change q (p (xor x y))=xor (q (p x)) (xor (q (p y)) (q (p (origin r))))
  rw [hp,←Holant.Tractable.AffinePhase.xor_assoc,affine_triple q hq,
    Holant.Tractable.AffinePhase.xor_assoc]

end
end Paper2.DegreeCSP.AffineSupportChart
