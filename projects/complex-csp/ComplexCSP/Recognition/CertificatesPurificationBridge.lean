import ComplexCSP.Recognition.CertificatesNumberFieldRoots
import ComplexCSP.Algebra.Purification

/-!
# Deriving every intrinsic certificate test from a purification map

The original values are represented by an injective multiplicative map into
actual number-field units. The complex realization is a field embedding.
Every local entry test is proved below from the structural purification-map
properties and the actual finite root alphabet; no `IntrinsicTests` hypothesis
is retained in the final theorem.
-/

namespace ComplexCSP.Certificates

open Purification
open scoped BigOperators

variable {K Γ X D : Type*} [Field K] [CommGroup Γ]

/-- The original field value of a nonzero group element. -/
def fieldValueHom (ρ : Γ →* Kˣ) : Γ →* K := (Units.coeHom K).comp ρ

@[simp] theorem fieldValueHom_apply (ρ : Γ →* Kˣ) (x : Γ) :
    fieldValueHom ρ x = (ρ x : K) := rfl

theorem fieldValueHom_injective (ρ : Γ →* Kˣ) (hρ : Function.Injective ρ) :
    Function.Injective (fieldValueHom ρ) := Units.val_injective.comp hρ

theorem fieldValueHom_ne_zero (ρ : Γ →* Kˣ) (x : Γ) : fieldValueHom ρ x ≠ 0 :=
  Units.ne_zero (ρ x)

/-- The complex original realization associated with a field embedding. -/
def complexOriginal (φ : K →+* ℂ) (ρ : Γ →* Kˣ) : Γ →* ℂˣ :=
  (Units.map φ.toMonoidHom).comp ρ

@[simp] theorem complexOriginal_val (φ : K →+* ℂ) (ρ : Γ →* Kˣ) (x : Γ) :
    (complexOriginal φ ρ x : ℂ) = φ (fieldValueHom ρ x) := rfl

/-- Zero-preserving original field entries. -/
def fieldEntry (ρ : Γ →* Kˣ) : Option Γ → K
  | none => 0
  | some x => fieldValueHom ρ x

@[simp] theorem fieldEntry_none (ρ : Γ →* Kˣ) : fieldEntry ρ none = 0 := rfl
@[simp] theorem fieldEntry_some (ρ : Γ →* Kˣ) (x : Γ) :
    fieldEntry ρ (some x) = fieldValueHom ρ x := rfl

@[simp] theorem fieldEntry_eq_zero_iff (ρ : Γ →* Kˣ) (a : Option Γ) :
    fieldEntry ρ a = 0 ↔ a = none := by
  cases a <;> simp

variable [NumberField K]

variable (φ : K →+* ℂ) (ρ : Γ →* Kˣ) (hρ : Function.Injective ρ)
variable (P : PurificationMap Γ (complexOriginal φ ρ))
include hρ

theorem value_norm_eq_iff_numberFieldRoot (a b : Γ) :
    ‖P.value a‖ = ‖P.value b‖ ↔
      ∃ r : NumberFieldRoots K, fieldValueHom ρ a =
        (numberFieldRootAlphabet K).value r * fieldValueHom ρ b := by
  rw [P.norm_eq_iff_torsion]
  constructor
  · intro ht
    obtain ⟨r, hr⟩ := numberFieldRoots_complete (fieldValueHom ρ (a / b))
      ((fieldValueHom ρ).isOfFinOrder ht)
    refine ⟨r, ?_⟩
    rw [hr, map_div, div_mul_cancel₀ _ (fieldValueHom_ne_zero ρ b)]
  · rintro ⟨r, hr⟩
    have hdiv : fieldValueHom ρ (a / b) = (numberFieldRootAlphabet K).value r := by
      rw [map_div]
      exact (div_eq_iff (fieldValueHom_ne_zero ρ b)).mpr hr
    apply (fieldValueHom_injective ρ hρ).isOfFinOrder_iff.mp
    rw [hdiv]
    exact numberFieldRoot_finite_order r

theorem value_root_covariance (a b : Γ) (r : NumberFieldRoots K)
    (h : fieldValueHom ρ a = (numberFieldRootAlphabet K).value r * fieldValueHom ρ b) :
    P.value a = φ ((numberFieldRootAlphabet K).value r) * P.value b := by
  have ht : IsOfFinOrder (a / b) := (P.norm_eq_iff_torsion a b).mp
    ((value_norm_eq_iff_numberFieldRoot φ ρ hρ P a b).mpr ⟨r, h⟩)
  have hratio : P.value a / P.value b = φ ((numberFieldRootAlphabet K).value r) := by
    rw [← P.value_div]
    change (P.hom (a / b) : ℂ) = _
    rw [P.fixes_torsion _ ht, complexOriginal_val]
    congr 1
    rw [map_div]
    exact (div_eq_iff (fieldValueHom_ne_zero ρ b)).mpr h
  exact (div_eq_iff (P.value_ne_zero b)).mp hratio

omit [NumberField K] in
theorem entry_eq_iff_fieldEntry (a b : Option Γ) :
    P.entry a = P.entry b ↔ fieldEntry ρ a = fieldEntry ρ b := by
  cases a with
  | none =>
    cases b with
    | none => simp
    | some b =>
      constructor
      · intro h
        exact False.elim (P.value_ne_zero b h.symm)
      · intro h
        exact False.elim (fieldValueHom_ne_zero ρ b h.symm)
  | some a =>
    cases b with
    | none => simp [P.value_ne_zero]
    | some b =>
      exact (P.value_eq_iff a b).trans (fieldValueHom_injective ρ hρ).eq_iff.symm

theorem entry_norm_eq_iff_numberFieldRoot (a b : Option Γ) :
    ‖P.entry a‖ = ‖P.entry b‖ ↔
      ∃ r : NumberFieldRoots K, fieldEntry ρ a =
        (numberFieldRootAlphabet K).value r * fieldEntry ρ b := by
  cases a with
  | none =>
    cases b with
    | none => simp
    | some b => simp
  | some a =>
    cases b with
    | none => simp [P.value_ne_zero]
    | some b => exact value_norm_eq_iff_numberFieldRoot φ ρ hρ P a b

theorem entry_root_covariance (a b : Option Γ) (r : NumberFieldRoots K)
    (h : fieldEntry ρ a = (numberFieldRootAlphabet K).value r * fieldEntry ρ b) :
    P.entry a = φ ((numberFieldRootAlphabet K).value r) * P.entry b := by
  cases a with
  | none =>
    cases b with
    | none => simp
    | some b =>
      have hn := mul_ne_zero (numberFieldRoot_ne_zero r) (fieldValueHom_ne_zero ρ b)
      exact False.elim (hn h.symm)
  | some a =>
    cases b with
    | none =>
      simp only [fieldEntry_none, fieldEntry_some, mul_zero] at h
      exact False.elim (fieldValueHom_ne_zero ρ a h)
    | some b => exact value_root_covariance φ ρ hρ P a b r h

omit hρ

/-- Multiplication with an absorbing zero option. -/
def optionProduct : Option Γ → Option Γ → Option Γ
  | some a, some b => some (a * b)
  | _, _ => none

omit [NumberField K] in
@[simp] theorem fieldEntry_optionProduct (a b : Option Γ) :
    fieldEntry ρ (optionProduct a b) = fieldEntry ρ a * fieldEntry ρ b := by
  cases a <;> cases b <;> simp [optionProduct, map_mul]

omit [NumberField K] in
@[simp] theorem entry_optionProduct (a b : Option Γ) :
    P.entry (optionProduct a b) = P.entry a * P.entry b := by
  cases a <;> cases b <;> simp [optionProduct, P.value_mul]

include hρ

omit [NumberField K] in
theorem entry_products_iff_field_products (a b c d : Option Γ) :
    P.entry a * P.entry b = P.entry c * P.entry d ↔
      fieldEntry ρ a * fieldEntry ρ b = fieldEntry ρ c * fieldEntry ρ d := by
  rw [← entry_optionProduct φ ρ P, ← entry_optionProduct φ ρ P,
    entry_eq_iff_fieldEntry φ ρ hρ P, fieldEntry_optionProduct, fieldEntry_optionProduct]

theorem entry_norm_products_iff_twisted (a b c d : Option Γ) :
    ‖P.entry a * P.entry b‖ = ‖P.entry c * P.entry d‖ ↔
      ∃ r : NumberFieldRoots K, fieldEntry ρ a * fieldEntry ρ b =
        (numberFieldRootAlphabet K).value r * (fieldEntry ρ c * fieldEntry ρ d) := by
  rw [← entry_optionProduct φ ρ P, ← entry_optionProduct φ ρ P,
    entry_norm_eq_iff_numberFieldRoot φ ρ hρ P,
    fieldEntry_optionProduct, fieldEntry_optionProduct]

/-- Every required intrinsic test is derived from the purification map and the
actual number field. No finite-root or local-entry-test hypotheses remain. -/
theorem intrinsicTests_of_purificationMap (T : X → D → Option Γ) :
    IntrinsicTests (numberFieldRootAlphabet K) (numberFieldRootRealization φ)
      (fun x z ↦ fieldEntry ρ (T x z)) (fun x z ↦ P.entry (T x z)) where
  zero x z := by rw [P.entry_eq_zero_iff, fieldEntry_eq_zero_iff]
  ordinary_minor x y z w :=
    entry_products_iff_field_products φ ρ hρ P (T x z) (T y w) (T x w) (T y z)
  magnitude_minor x y z w :=
    entry_norm_products_iff_twisted φ ρ hρ P (T x z) (T y w) (T x w) (T y z)
  root_covariance x z w r h := entry_root_covariance φ ρ hρ P (T x z) (T x w) r h
  magnitude_anchor x z w _ := entry_norm_eq_iff_numberFieldRoot φ ρ hρ P (T x z) (T x w)

end ComplexCSP.Certificates
