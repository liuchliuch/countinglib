import Paper2.DegreeCSP.AffineSupportCoordinates
import Paper2.DegreeCSP.GeneratedCoordinateMarginal

/-! Actual original coordinates on a nonempty xor-closed Boolean support.
Translation by a supported word identifies the live words with the retained
support-direction subspace, and the proved coordinate basis then supplies a
bijective Boolean projection. No gadget realization is used. -/
namespace Paper2.DegreeCSP.AffineLiveCoordinates
open Tractable
open Holant.ReedMuller.FlatNetwork (vectorWord wordVector boolEquiv vector_word word_vector)
open Holant.Tractable.AffinePhase (Word xor)
open Holant.ReedMuller.AffinePatching (supportDirections)
open GeneratedCoordinateMarginal (Live liveProjection)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {n : ℕ}

private theorem vector_self_add (v : Fin n→ZMod 2) : v+v=0 := by
  funext j
  exact CharTwo.add_self_eq_zero (v j)

/-- Translate the genuine linear support directions onto the original live
Boolean words. The inverse is the same translation in characteristic two. -/
def directionLiveEquiv (f : Signature AlgebraicComplex n) (a : Word n) (ha : f a≠0)
    (ht : ∀ x y z : Word n,f x≠0→f y≠0→f z≠0→f (xor (xor x y) z)≠0) :
    supportDirections f a ha ht ≃ Live f where
  toFun v := ⟨wordVector (vectorWord a+v.val),v.property⟩
  invFun x := ⟨vectorWord a+vectorWord x.val,by
    change f (wordVector (vectorWord a+(vectorWord a+vectorWord x.val)))≠0
    simpa only [←add_assoc,vector_self_add,zero_add,word_vector] using x.property⟩
  left_inv v := by
    apply Subtype.ext
    change vectorWord a+vectorWord (wordVector (vectorWord a+v.val))=v.val
    simp only [vector_word,←add_assoc,vector_self_add,zero_add]
  right_inv x := by
    apply Subtype.ext
    change wordVector (vectorWord a+(vectorWord a+vectorWord x.val))=x.val
    simp only [←add_assoc,vector_self_add,zero_add,word_vector]

/-- Translate selected field coordinates and read their actual Boolean values. -/
def translatedCoordinates {r : ℕ} (a : Word n) (q : Fin r→Fin n) :
    (Fin r→ZMod 2) ≃ (Fin r→Bool) where
  toFun v j := boolEquiv.symm (vectorWord a (q j)+v j)
  invFun b j := vectorWord a (q j)+boolEquiv (b j)
  left_inv v := by
    funext j
    simp only [Equiv.apply_symm_apply]
    rw [←add_assoc,CharTwo.add_self_eq_zero,zero_add]
  right_inv b := by
    funext j
    change boolEquiv.symm (vectorWord a (q j)+(vectorWord a (q j)+boolEquiv (b j)))=b j
    rw [←add_assoc,CharTwo.add_self_eq_zero,zero_add,Equiv.symm_apply_apply]

/-- The selected coordinate projection is a bijection on the literal live
support, with no coefficient transformation or decoding assumption. -/
theorem exists_live_coordinates (f : Signature AlgebraicComplex n)
    (a : Word n) (ha : f a≠0)
    (ht : ∀ x y z : Word n,f x≠0→f y≠0→f z≠0→f (xor (xor x y) z)≠0) :
    ∃ (r : ℕ) (q : Fin r→Fin n),Function.Injective q ∧
      Function.Bijective (liveProjection f q) := by
  obtain ⟨r,q,hq,hproj⟩ := AffineSupportCoordinates.subspace_coordinates
    (supportDirections f a ha ht)
  let e := directionLiveEquiv f a ha ht
  let t := translatedCoordinates a q
  have hcomp := t.bijective.comp (hproj.comp e.symm.bijective)
  have he : (fun x : Live f=>t (fun j=>(e.symm x).val (q j)))=liveProjection f q := by
    funext x j
    change boolEquiv.symm (vectorWord a (q j)+(vectorWord a (q j)+vectorWord x.val (q j)))=
      x.val (q j)
    rw [←add_assoc,CharTwo.add_self_eq_zero,zero_add]
    exact boolEquiv.symm_apply_apply _
  refine ⟨r,q,hq,?_⟩
  simpa only [Function.comp_def,he] using hcomp

/-- The pure xor-preservation endpoint uses the same actual support and live
subtype as the exact generated-coordinate marginal theorem. -/
theorem exists_live_coordinates_xor (f : Signature AlgebraicComplex n)
    (a : Fin n→Bool) (ha : f a≠0)
    (hxor : BooleanStructure.Preserves BooleanStructure.xor3 {x | f x≠0}) :
    ∃ (r : ℕ) (q : Fin r→Fin n),Function.Injective q ∧
      Function.Bijective (liveProjection f q) := by
  apply exists_live_coordinates f a ha
  intro x y z hx hy hz
  exact hxor x hx y hy z hz

end
end Paper2.DegreeCSP.AffineLiveCoordinates
