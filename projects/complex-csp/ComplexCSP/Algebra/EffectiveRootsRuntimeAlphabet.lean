import ComplexCSP.Algebra.EffectiveRootsCoefficients
import ComplexCSP.Recognition.CertificatesExponentRoots
import Mathlib.Logic.Encodable.Basic

/-!
# Runtime finite root alphabets with proof-only presentation certificates

The executable data are a dimension, integer polynomial tail, and field
generator. A semantic power-basis/minimal-polynomial witness certifies this
input, but is used only in proofs. Root enumeration is the computed coordinate
list, not `Fintype.ofFinite`; encoding is a subtype encoding, not
`Encodable.ofFinite`.
-/

namespace ComplexCSP.EffectiveRoots

variable {K : Type*} [Field K] [NumberField K]

/-- A genuine certified integral presentation. It contains neither a root list
nor an assumed enumeration-completeness property. -/
def IntegralPresentation (n : ℕ) (a : Fin n → ℤ) (α : K) : Prop :=
  ∃ b : Module.Basis (Fin n) ℚ K, (∀ i, b i = α ^ i.val) ∧
    ∃ p : Polynomial ℤ, p.Monic ∧ Polynomial.aeval α p = 0 ∧
      p.map (Int.castRingHom ℚ) = minpoly ℚ α ∧ ∀ i : Fin n, p.coeff i.val = a i

theorem integralPresentation_of_powerBasis (pb : PowerBasis ℚ K) (p : Polynomial ℤ)
    (hp : p.Monic) (hroot : Polynomial.aeval pb.gen p = 0)
    (hpoly : p.map (Int.castRingHom ℚ) = minpoly ℚ pb.gen)
    (a : Fin pb.dim → ℤ) (hcoeff : ∀ i : Fin pb.dim, p.coeff i.val = a i) :
    IntegralPresentation pb.dim a pb.gen :=
  ⟨pb.basis, pb.basis_eq_pow, p, hp, hroot, hpoly, hcoeff⟩

theorem presentation_root_mem_iff {n : ℕ} {a : Fin n → ℤ} {α : K}
    (h : IntegralPresentation n a α) (v : EncodedNumberField.CoeffVector n) :
    v ∈ rootCoordinatesFromCoefficients n a ↔ IsOfFinOrder (EncodedNumberField.interpret α v) := by
  obtain ⟨b, hb, p, hp, hroot, hpoly, hcoeff⟩ := h
  let pb : PowerBasis ℚ K := ⟨α, n, b, hb⟩
  exact mem_rootCoordinatesFromCoefficients_iff pb p hp hroot hpoly a hcoeff v

theorem presentation_rootExponent_ge_two {n : ℕ} {a : Fin n → ℤ} {α : K}
    (h : IntegralPresentation n a α) : 2 ≤ rootExponentFromCoefficients n a := by
  obtain ⟨b, hb, p, hp, hroot, hpoly, hcoeff⟩ := h
  let pb : PowerBasis ℚ K := ⟨α, n, b, hb⟩
  exact rootExponentFromCoefficients_ge_two pb p hp hroot hpoly a hcoeff

theorem presentation_rootExponent_killsTorsion {n : ℕ} {a : Fin n → ℤ} {α : K}
    (h : IntegralPresentation n a α) :
    RowDetector.KillsTorsion K (rootExponentFromCoefficients n a) := by
  obtain ⟨b, hb, p, hp, hroot, hpoly, hcoeff⟩ := h
  let pb : PowerBasis ℚ K := ⟨α, n, b, hb⟩
  exact rootExponentFromCoefficients_killsTorsion pb p hp hroot hpoly a hcoeff

theorem presentation_every_root {n : ℕ} {a : Fin n → ℤ} {α : K}
    (h : IntegralPresentation n a α) (ζ : K) (hζ : IsOfFinOrder ζ) :
    ∃ v ∈ rootCoordinatesFromCoefficients n a, EncodedNumberField.interpret α v = ζ := by
  obtain ⟨b, hb, p, hp, hroot, hpoly, hcoeff⟩ := h
  let pb : PowerBasis ℚ K := ⟨α, n, b, hb⟩
  refine ⟨pb.basis.equivFun ζ, ?_, EncodedNumberField.interpret_coordinates pb ζ⟩
  apply (mem_rootCoordinatesFromCoefficients_iff pb p hp hroot hpoly a hcoeff _).mpr
  simpa only [EncodedNumberField.interpret_coordinates] using hζ

/-- The forward map of the computed coordinate list into the runtime root type.
Every runtime operation is on coordinates or the supplied field operations. -/
def rootFromCoordinate {n : ℕ} (a : Fin n → ℤ) (α : K)
    (h : IntegralPresentation n a α) (v : ↥(rootCoordinatesFromCoefficients n a)) :
    rootsOfUnity (rootExponentFromCoefficients n a) K :=
  let hz := (presentation_root_mem_iff h v.val).mp v.property
  ⟨Units.mk0 (EncodedNumberField.interpret α v.val) hz.isUnit.ne_zero,
    (mem_rootsOfUnity' _ _).mpr (presentation_rootExponent_killsTorsion h _ hz)⟩

/-- Actual runtime enumeration of the root subtype, directly from the finite
computed coordinate list. No abstract finite-choice enumeration is used. -/
def runtimeRootFintype [DecidableEq K] {n : ℕ} (a : Fin n → ℤ) (α : K)
    (h : IntegralPresentation n a α) : Fintype (rootsOfUnity (rootExponentFromCoefficients n a) K) where
  elems := (rootCoordinatesFromCoefficients n a).attach.image (rootFromCoordinate a α h)
  complete r := by
    have hE : 0 < rootExponentFromCoefficients n a :=
      lt_of_lt_of_le (by decide) (presentation_rootExponent_ge_two h)
    have hr : IsOfFinOrder (r.val : K) :=
      isOfFinOrder_iff_pow_eq_one.mpr
        ⟨rootExponentFromCoefficients n a, hE, (mem_rootsOfUnity' _ _).mp r.property⟩
    obtain ⟨v, hv, heq⟩ := presentation_every_root h (r.val : K) hr
    apply Finset.mem_image.mpr
    refine ⟨⟨v, hv⟩, Finset.mem_attach _ _, ?_⟩
    apply Subtype.ext
    apply Units.ext
    exact heq

/-- Root scalars form a directly encodable subtype of the executable field. -/
def rootScalarEquiv (E : ℕ) (hE : 0 < E) :
    rootsOfUnity E K ≃ {z : K // z ^ E = 1} where
  toFun r := ⟨r.val, (mem_rootsOfUnity' _ _).mp r.property⟩
  invFun z := ⟨Units.mk0 z.val (by
    intro hz
    have hh := z.property
    rw [hz, zero_pow (ne_of_gt hE)] at hh
    exact zero_ne_one hh), (mem_rootsOfUnity' _ _).mpr z.property⟩
  left_inv r := by apply Subtype.ext; apply Units.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

/-- Runtime encoding uses only the source field's actual encoding and a
computable power/equality check. It does not call `Encodable.ofFinite`. -/
def runtimeRootEncodable [DecidableEq K] [Encodable K] {n : ℕ}
    (a : Fin n → ℤ) (α : K) (h : IntegralPresentation n a α) :
    Encodable (rootsOfUnity (rootExponentFromCoefficients n a) K) :=
  Encodable.ofEquiv {z : K // z ^ rootExponentFromCoefficients n a = 1}
    (rootScalarEquiv _ (lt_of_lt_of_le (by decide) (presentation_rootExponent_ge_two h)))

/-- The finite certificate-program alphabet can now use the actual computed
runtime exponent and runtime enumeration. -/
def runtimeRootAlphabet {n : ℕ} (a : Fin n → ℤ) :
    Certificates.RootAlphabet K (rootsOfUnity (rootExponentFromCoefficients n a) K) :=
  Certificates.exponentRootAlphabet K (rootExponentFromCoefficients n a)

end ComplexCSP.EffectiveRoots
