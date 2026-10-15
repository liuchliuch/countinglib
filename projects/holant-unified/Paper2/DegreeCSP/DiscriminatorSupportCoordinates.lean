import Paper2.DegreeCSP.DiscriminatorCoordinate
import Paper2.DegreeCSP.BooleanDiscriminatorAffine
import Paper2.DegreeCSP.AffineLiveCoordinates
import Paper2.DegreeCSP.MultiCoordinateContext

/-! Explicit coordinate expressions for the actual nonzero support of a
discriminator-preserved signature. The selected projection is a bijection;
its inverse preserves discriminator and therefore every decoded coordinate
is a constant or one selected coordinate with a fixed Boolean flip.
-/
namespace Paper2.DegreeCSP.DiscriminatorSupportCoordinates
open Tractable BooleanStructure
open GeneratedCoordinateMarginal (Live liveProjection)
open MultiCoordinateContext (Expr eval word)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {n r : ℕ}

/-- The inverse of an actual live-coordinate projection has a literal
expression at every port, and selected ports use the unflipped variable. -/
theorem expressions_of_projection (f : Signature AlgebraicComplex n)
    (q : Fin r → Fin n) (hq : Function.Injective q)
    (bijective : Function.Bijective (liveProjection f q))
    (hd : Preserves discriminator {w | f w ≠ 0}) :
    ∃ E : Fin n → Expr r,
      (∀ j, E (q j) = Sum.inr (j,false)) ∧
      (∀ x, f (word E x) ≠ 0) ∧
      (∀ x j, word E x (q j) = x j) ∧
      (∀ w, f w ≠ 0 → word E (fun j => w (q j)) = w) := by
  classical
  let C : Live f ≃ (Fin r → Bool) := Equiv.ofBijective (liveProjection f q) bijective
  let decode : (Fin r → Bool) → Live f := C.symm
  have selected (x : Fin r → Bool) (j : Fin r) : (decode x).val (q j) = x j :=
    congrFun (C.apply_symm_apply x) j
  have decoder_hom (i : Fin n) :
      DiscriminatorCoordinate.Hom discriminator (fun x => (decode x).val i) := by
    intro x y z
    let w : Live f := ⟨fun j => discriminator
      ((decode x).val j,(decode y).val j,(decode z).val j),
      hd (decode x).val (decode x).property
        (decode y).val (decode y).property (decode z).val (decode z).property⟩
    have projection : C w = fun j => discriminator (x j,y j,z j) := by
      funext j
      change discriminator ((decode x).val (q j),(decode y).val (q j),
        (decode z).val (q j)) = _
      rw [selected,selected,selected]
    have recovered : decode (fun j => discriminator (x j,y j,z j)) = w := by
      apply C.injective
      rw [C.apply_symm_apply,projection]
    exact congrArg (fun v : Live f => v.val i) recovered
  have representation (i : Fin n) :
      ∃ e : Expr r, ∀ x, eval e x = (decode x).val i := by
    rcases DiscriminatorCoordinate.classify (fun x => (decode x).val i) (decoder_hom i) with
      ⟨b,hb⟩ | ⟨j,b,hb⟩
    · exact ⟨Sum.inl b,fun x => (hb x).symm⟩
    · exact ⟨Sum.inr (j,b),fun x => (hb x).symm⟩
  let E : Fin n → Expr r := fun i =>
    if hi : i ∈ Set.range q then Sum.inr (Classical.choose hi,false)
    else Classical.choose (representation i)
  have literal (j : Fin r) : E (q j) = Sum.inr (j,false) := by
    have hj : q j ∈ Set.range q := ⟨j,rfl⟩
    simp only [E,dite_eq_left hj]
    rw [hq (Classical.choose_spec hj)]
  have decoded (x : Fin r → Bool) : word E x = (decode x).val := by
    funext i
    by_cases hi : i ∈ Set.range q
    · have hqi := Classical.choose_spec hi
      change eval (E i) x = _
      simp only [E,dite_eq_left hi,eval,Bool.xor_false]
      exact (selected x (Classical.choose hi)).symm.trans (congrArg (decode x).val hqi)
    · change eval (E i) x = _
      simp only [E,dite_eq_right hi]
      exact Classical.choose_spec (representation i) x
  refine ⟨E,literal,?_,?_,?_⟩
  · intro x
    rw [decoded]
    exact (decode x).property
  · intro x j
    rw [decoded]
    exact selected x j
  · intro w hw
    rw [decoded]
    exact congrArg Subtype.val (C.symm_apply_apply (⟨w,hw⟩ : Live f))

/-- Every nonempty discriminator-preserved support has an explicit signed
coordinate decoder using actual independent original ports. -/
theorem exists_coordinates_literal (f : Signature AlgebraicComplex n)
    (z : Fin n → Bool) (hz : f z ≠ 0)
    (hd : Preserves discriminator {w | f w ≠ 0}) :
    ∃ (r : ℕ) (q : Fin r → Fin n) (E : Fin n → Expr r),
      Function.Injective q ∧
      (∀ j, E (q j) = Sum.inr (j,false)) ∧
      (∀ x, f (word E x) ≠ 0) ∧
      (∀ x j, word E x (q j) = x j) ∧
      (∀ w, f w ≠ 0 → word E (fun j => w (q j)) = w) := by
  obtain ⟨r,q,hq,hbij⟩ := AffineLiveCoordinates.exists_live_coordinates_xor f z hz
    (preserves_xor_of_discriminator _ hd)
  obtain ⟨E,hE,hlive,hselected,hrecover⟩ := expressions_of_projection f q hq hbij hd
  exact ⟨r,q,E,hq,hE,hlive,hselected,hrecover⟩

theorem exists_coordinates (f : Signature AlgebraicComplex n)
    (z : Fin n → Bool) (hz : f z ≠ 0)
    (hd : Preserves discriminator {w | f w ≠ 0}) :
    ∃ (r : ℕ) (q : Fin r → Fin n) (E : Fin n → Expr r),
      Function.Injective q ∧
      (∀ x, f (word E x) ≠ 0) ∧
      (∀ x j, word E x (q j) = x j) ∧
      (∀ w, f w ≠ 0 → word E (fun j => w (q j)) = w) := by
  obtain ⟨r,q,E,hq,_,hlive,hselected,hrecover⟩ := exists_coordinates_literal f z hz hd
  exact ⟨r,q,E,hq,hlive,hselected,hrecover⟩

end
end Paper2.DegreeCSP.DiscriminatorSupportCoordinates

