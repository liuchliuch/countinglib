import ComplexCSP.Recognition.CertificatesPurificationBridge
import ComplexCSP.Algebra.LegalPurificationChoices

/-!
# Lifting legal purification groups into a working subfield

Containment of the finite generating values in a complex subfield implies
containment of their whole multiplicative group. The resulting injective unit
lift identifies the source realization exactly, so all certificate entry tests
apply to the actual prime-based legal purification map.
-/

namespace ComplexCSP.Certificates

open Purification

/-- Complex units whose underlying values belong to a fixed subfield. -/
def unitsInSubfield (K : Subfield ℂ) : Subgroup ℂˣ where
  carrier := {x | (x : ℂ) ∈ K}
  one_mem' := K.one_mem
  mul_mem' ha hb := K.mul_mem ha hb
  inv_mem' := by
    intro x hx
    change ((x⁻¹ : ℂˣ) : ℂ) ∈ K
    simpa only [Units.val_inv_eq_inv_val] using K.inv_mem hx

/-- The canonical injective lift of a complex subgroup into subfield units. -/
noncomputable def groupLift (K : Subfield ℂ) (Γ : Subgroup ℂˣ)
    (hΓ : Γ ≤ unitsInSubfield K) : Γ →* Kˣ where
  toFun x := Units.mk0 ⟨(x.val : ℂ), hΓ x.property⟩ (by
    intro h
    exact Units.ne_zero x.val (congrArg Subtype.val h))
  map_one' := by apply Units.ext; apply Subtype.ext; rfl
  map_mul' _ _ := by apply Units.ext; apply Subtype.ext; rfl

@[simp] theorem groupLift_val (K : Subfield ℂ) (Γ : Subgroup ℂˣ)
    (hΓ : Γ ≤ unitsInSubfield K) (x : Γ) :
    (((groupLift K Γ hΓ x : Kˣ) : K) : ℂ) = (x.val : ℂ) := rfl

theorem groupLift_injective (K : Subfield ℂ) (Γ : Subgroup ℂˣ)
    (hΓ : Γ ≤ unitsInSubfield K) : Function.Injective (groupLift K Γ hΓ) := by
  intro x y h
  apply Subtype.ext
  apply Units.ext
  exact congrArg (fun u : Kˣ ↦ ((u : K) : ℂ)) h

@[simp] theorem complexOriginal_groupLift (K : Subfield ℂ) (Γ : Subgroup ℂˣ)
    (hΓ : Γ ≤ unitsInSubfield K) :
    complexOriginal K.subtype (groupLift K Γ hΓ) = Γ.subtype := by
  apply MonoidHom.ext
  intro x
  apply Units.ext
  rfl

/-- All multiplicative combinations of finite ambient values stay in their
working field, including inverse powers. -/
theorem closure_le_unitsInSubfield (K : Subfield ℂ) (S : Finset ℂˣ)
    (hS : ∀ x ∈ S, (x : ℂ) ∈ K) : Subgroup.closure (↑S : Set ℂˣ) ≤ unitsInSubfield K := by
  apply (Subgroup.closure_le _).mpr
  intro x hx
  exact hS x hx

/-- Regard the same purification homomorphism as a field-based realization.
This changes no purified value; it only identifies the source maps. -/
noncomputable def subfieldPurificationMap (K : Subfield ℂ) (Γ : Subgroup ℂˣ)
    (hΓ : Γ ≤ unitsInSubfield K) (P : PurificationMap Γ Γ.subtype) :
    PurificationMap Γ (complexOriginal K.subtype (groupLift K Γ hΓ)) where
  hom := P.hom
  injective := P.injective
  fixes_torsion x hx := by
    rw [complexOriginal_groupLift]
    exact P.fixes_torsion x hx
  norm_one_iff := P.norm_one_iff

@[simp] theorem subfieldPurificationMap_entry (K : Subfield ℂ) (Γ : Subgroup ℂˣ)
    (hΓ : Γ ≤ unitsInSubfield K) (P : PurificationMap Γ Γ.subtype) (a : Option Γ) :
    (subfieldPurificationMap K Γ hΓ P).entry a = P.entry a := rfl

/-- The actual source-group torsion is killed by the proved number-field
exponent, expressed directly on its original complex values. -/
theorem group_torsion_pow_eq_one (K : Subfield ℂ) [NumberField K]
    (Γ : Subgroup ℂˣ) (hΓ : Γ ≤ unitsInSubfield K) (x : Γ) (hx : IsOfFinOrder x) :
    (x.val : ℂ) ^ RowDetector.fieldExponent K = 1 := by
  have hfield := (fieldValueHom (groupLift K Γ hΓ)).isOfFinOrder hx
  have hp := RowDetector.fieldExponent_killsTorsion K _ hfield
  have hc := congrArg K.subtype hp
  simp only [map_pow, map_one, fieldValueHom_apply] at hc
  exact hc

/-- All intrinsic tests for an actual subgroup purification in its number field.
Every test follows from map laws and the finite root theorem. -/
theorem intrinsicTests_subfield (K : Subfield ℂ) [NumberField K]
    (Γ : Subgroup ℂˣ) (hΓ : Γ ≤ unitsInSubfield K) (P : PurificationMap Γ Γ.subtype)
    {X D : Type*} (T : X → D → Option Γ) :
    IntrinsicTests (numberFieldRootAlphabet K) (numberFieldRootRealization K.subtype)
      (fun x z ↦ fieldEntry (groupLift K Γ hΓ) (T x z)) (fun x z ↦ P.entry (T x z)) :=
  intrinsicTests_of_purificationMap K.subtype (groupLift K Γ hΓ)
    (groupLift_injective K Γ hΓ) (subfieldPurificationMap K Γ hΓ P) T

/-- Specialize the derived tests to the actual arbitrary-legal-choice prime
purification constructed in `LegalPurificationChoices`. -/
theorem intrinsicTests_legalChoice (K : Subfield ℂ) [NumberField K]
    (S : Finset ℂˣ) (hS : ∀ x ∈ S, (x : ℂ) ∈ K)
    (L : GeneratingSet.LegalGeneratingSet S) {X D : Type*}
    (T : X → D → Option (GeneratingSet.LegalGeneratingSet.EntryGroup S)) :
    IntrinsicTests (numberFieldRootAlphabet K) (numberFieldRootRealization K.subtype)
      (fun x z ↦ fieldEntry (groupLift K _ (closure_le_unitsInSubfield K S hS)) (T x z))
      (fun x z ↦ L.purificationMap.entry (T x z)) := by
  exact intrinsicTests_subfield K _ (closure_le_unitsInSubfield K S hS) L.purificationMap T

end ComplexCSP.Certificates
