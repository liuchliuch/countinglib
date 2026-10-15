import Paper2.DegreeCSP.BooleanAffineParityMinorCoordinates
import Paper2.DegreeCSP.BooleanAffineParityMinorSimple

/-! A nonproduct affine relation has a genuine ternary parity minor. The minor
uses two independent original coordinates, one original dependent coordinate,
literal pins on the other independent coordinates, and existential projection.
-/
namespace Paper2.DegreeCSP.BooleanAffineParityMinor
open Tractable
open BooleanStructure (indicator)
open Holant.ReedMuller.FlatNetwork (vectorWord wordVector boolEquiv vector_word word_vector)
open Holant.ReedMuller.AffinePatching (supportDirections)
open Holant.Tractable.AffinePhase (Word xor)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {n r : ℕ}

def relationLiveEquiv (R : Set (Fin n → Bool)) :
    GeneratedCoordinateMarginal.Live (indicator R) ≃ {x // x ∈ R} where
  toFun x := ⟨x.val, (BooleanStructure.indicator_ne_zero R x.val).mp x.property⟩
  invFun x := ⟨x.val, (BooleanStructure.indicator_ne_zero R x.val).mpr x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem relation_ternary (R : Set (Fin n → Bool))
    (hxor : BooleanStructure.Preserves BooleanStructure.xor3 R) :
    ∀ x y z : Word n, indicator R x ≠ 0 → indicator R y ≠ 0 → indicator R z ≠ 0 →
      indicator R (xor (xor x y) z) ≠ 0 := by
  intro x y z hx hy hz
  apply (BooleanStructure.indicator_ne_zero R _).mpr
  exact hxor x ((BooleanStructure.indicator_ne_zero R x).mp hx)
    y ((BooleanStructure.indicator_ne_zero R y).mp hy)
    z ((BooleanStructure.indicator_ne_zero R z).mp hz)

/-- Any bijective selection of actual live coordinates also gives a genuine
linear coordinate isomorphism on the translated support directions. -/
theorem directions_projection_bijective (R : Set (Fin n → Bool))
    (a : Fin n → Bool) (ha : a ∈ R)
    (hxor : BooleanStructure.Preserves BooleanStructure.xor3 R)
    (q : Fin r → Fin n)
    (hproj : Function.Bijective (fun x : {x // x ∈ R} => fun j => x.val (q j))) :
    Function.Bijective (fun v : supportDirections (indicator R) a
      ((BooleanStructure.indicator_ne_zero R a).mpr ha) (relation_ternary R hxor) =>
        fun j => v.val (q j)) := by
  let ha' := (BooleanStructure.indicator_ne_zero R a).mpr ha
  let ht := relation_ternary R hxor
  let de := (AffineLiveCoordinates.directionLiveEquiv (indicator R) a ha' ht).trans
    (relationLiveEquiv R)
  constructor
  · intro u v huv
    apply de.injective
    apply hproj.injective
    funext j
    change boolEquiv.symm (boolEquiv (a (q j)) + u.val (q j)) =
      boolEquiv.symm (boolEquiv (a (q j)) + v.val (q j))
    have he := congrFun huv j
    change u.val (q j) = v.val (q j) at he
    rw [he]
  · intro z
    obtain ⟨x, hx⟩ := hproj.surjective (fun j => boolEquiv.symm (boolEquiv (a (q j)) + z j))
    refine ⟨de.symm x, ?_⟩
    funext j
    change boolEquiv (a (q j)) + boolEquiv (x.val (q j)) = z j
    have he := congrArg boolEquiv (congrFun hx j)
    rw [Equiv.apply_symm_apply] at he
    rw [he, ←add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- The parity minor can use a previously selected coordinate basis. Thus its
four nonzero fibers are the same exact fibers as a coefficient marginal. -/
theorem exists_parity_minor_on_coordinates (R : Set (Fin n → Bool))
    (a : Fin n → Bool) (ha : a ∈ R)
    (hxor : BooleanStructure.Preserves BooleanStructure.xor3 R)
    (hnon : ¬ Product (indicator R)) (q : Fin r → Fin n)
    (hproj : Function.Bijective (fun x : {x // x ∈ R} => fun j => x.val (q j))) :
    ∃ (i j : Fin r) (t : Fin n), i ≠ j ∧ t ≠ q i ∧ t ≠ q j ∧
      ∀ z, PinnedProjection R a q i j t z ↔
        z 2 = Bool.xor (Bool.xor (z 0) (z 1))
          (Bool.xor (Bool.xor (a (q i)) (a (q j))) (a t)) := by
  classical
  let ha' := (BooleanStructure.indicator_ne_zero R a).mpr ha
  let ht := relation_ternary R hxor
  let D := supportDirections (indicator R) a ha' ht
  have hD := directions_projection_bijective R a ha hxor q hproj
  let e := coordinateEquiv D q hD
  let p := parameterWord a e
  let L := coordinateForm e
  have hp : ∀ v t, p v t = boolEquiv.symm (boolEquiv (a t) + L t v) :=
    parameterWord_coordinate a e
  have hselected : ∀ v j, L (q j) v = v j := coordinateForm_selected D q hD
  have hmem : ∀ v, p v ∈ R := by
    intro v
    apply (BooleanStructure.indicator_ne_zero R _).mp
    exact (e.symm v).property
  have hsurj : ∀ x ∈ R, ∃ v, p v = x := by
    intro x hx
    let de := AffineLiveCoordinates.directionLiveEquiv (indicator R) a ha' ht
    let live : GeneratedCoordinateMarginal.Live (indicator R) :=
      ⟨x, (BooleanStructure.indicator_ne_zero R x).mpr hx⟩
    refine ⟨e (de.symm live), ?_⟩
    change (de (e.symm (e (de.symm live)))).val = x
    rw [e.symm_apply_apply, de.apply_symm_apply]
  obtain ⟨t, i, j, hij, hi, hj⟩ :=
    BooleanAffineParityMinorSimple.exists_nonsimple_coordinate R hnon p a L hp hmem hsurj
  have hti : t ≠ q i := by
    intro he
    rw [he, hselected] at hj
    have hzero : (Pi.single j 1 : Fin r → ZMod 2) i = 0 := by simp [hij]
    exact zero_ne_one (hzero.symm.trans hj)
  have htj : t ≠ q j := by
    intro he
    rw [he, hselected] at hi
    have hzero : (Pi.single i 1 : Fin r → ZMod 2) j = 0 := by simp [hij.symm]
    exact zero_ne_one (hzero.symm.trans hi)
  exact ⟨i, j, t, hij, hti, htj,
    pinned_projection_parity R a q p L hp hselected hmem hsurj hij t hi hj⟩

/-- The nonempty xor-closed relation itself supplies independent coordinates;
no pp definability, character extension, or gadget witness is assumed. -/
theorem exists_parity_minor (R : Set (Fin n → Bool)) (hne : R.Nonempty)
    (hxor : BooleanStructure.Preserves BooleanStructure.xor3 R)
    (hnon : ¬ Product (indicator R)) :
    ∃ (a : Fin n → Bool) (r : ℕ) (q : Fin r → Fin n), a ∈ R ∧
      Function.Injective q ∧
      Function.Bijective (fun x : {x // x ∈ R} => fun j => x.val (q j)) ∧
      ∃ (i j : Fin r) (t : Fin n), i ≠ j ∧ t ≠ q i ∧ t ≠ q j ∧
        ∀ z, PinnedProjection R a q i j t z ↔
          z 2 = Bool.xor (Bool.xor (z 0) (z 1))
            (Bool.xor (Bool.xor (a (q i)) (a (q j))) (a t)) := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨r, q, hq, hp⟩ := AffineLiveCoordinates.exists_live_coordinates_xor
    (indicator R) a ((BooleanStructure.indicator_ne_zero R a).mpr ha) (by
      intro x hx y hy z hz
      exact (BooleanStructure.indicator_ne_zero R _).mpr
        (hxor x ((BooleanStructure.indicator_ne_zero R x).mp hx)
          y ((BooleanStructure.indicator_ne_zero R y).mp hy)
          z ((BooleanStructure.indicator_ne_zero R z).mp hz)))
  have hrel : Function.Bijective (fun x : {x // x ∈ R} => fun j => x.val (q j)) := by
    exact hp.comp (relationLiveEquiv R).symm.bijective
  exact ⟨a, r, q, ha, hq, hrel,
    exists_parity_minor_on_coordinates R a ha hxor hnon q hrel⟩

/-- Exact uniqueness in the literal relation subtype used by the parity
endpoint. For `R = {x | f x ≠ 0}`, this is the actual `Live f` projection. -/
theorem pinned_projection_unique_relation (R : Set (Fin n → Bool)) (a : Fin n → Bool)
    (q : Fin r → Fin n)
    (hproj : Function.Injective (fun x : {x // x ∈ R} => fun j => x.val (q j)))
    (i j : Fin r) (z : Fin 3 → Bool) (x y : Fin n → Bool)
    (hx : x ∈ R) (hy : y ∈ R)
    (hxi : x (q i) = z 0) (hyi : y (q i) = z 0)
    (hxj : x (q j) = z 1) (hyj : y (q j) = z 1)
    (hxp : Pinned a q i j x) (hyp : Pinned a q i j y) : x = y := by
  have he : (⟨x, hx⟩ : {x // x ∈ R}) = ⟨y, hy⟩ := by
    apply hproj
    funext ℓ
    by_cases hli : ℓ = i
    · subst ℓ
      exact hxi.trans hyi.symm
    · by_cases hlj : ℓ = j
      · subst ℓ
        exact hxj.trans hyj.symm
      · exact (hxp ℓ hli hlj).trans (hyp ℓ hli hlj).symm
  exact congrArg Subtype.val he

end
end Paper2.DegreeCSP.BooleanAffineParityMinor
