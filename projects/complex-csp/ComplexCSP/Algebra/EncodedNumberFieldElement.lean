import ComplexCSP.Algebra.EncodedNumberFieldMaterialized
import Mathlib.Logic.Encodable.Pi
import Mathlib.Data.Rat.Encodable

/-! # A distinct executable field-element carrier

Only rational coordinates are stored. The relation coefficients remain runtime
parameters, preventing collision with the pointwise ring on functions. Semantic
power-basis witnesses are used exclusively to establish the algebraic laws.
-/
namespace ComplexCSP.EncodedNumberField

/-- A distinct carrier for arithmetic modulo the supplied monic relation. -/
@[ext] structure Element (n : ℕ) (c : CoeffVector n) where
  coeff : CoeffVector n
  deriving DecidableEq

namespace Element
variable {n : ℕ} {c : CoeffVector n}

instance : Encodable (Element n c) :=
  Encodable.ofEquiv (CoeffVector n) ⟨coeff, Element.mk, fun _ => rfl, fun _ => rfl⟩

instance : Zero (Element n c) := ⟨⟨EncodedNumberField.zero n⟩⟩
instance : One (Element n c) := ⟨⟨EncodedNumberField.one n⟩⟩
instance : Add (Element n c) := ⟨fun a b => ⟨EncodedNumberField.add a.coeff b.coeff⟩⟩
instance : Neg (Element n c) := ⟨fun a => ⟨EncodedNumberField.neg a.coeff⟩⟩
instance : Sub (Element n c) := ⟨fun a b => a + -b⟩
instance : Mul (Element n c) := ⟨fun a b => ⟨EncodedNumberField.materializedMul c a.coeff b.coeff⟩⟩
instance : Inv (Element n c) := ⟨fun a => ⟨EncodedNumberField.materializedInverse c a.coeff⟩⟩
instance : Div (Element n c) := ⟨fun a b => a * b⁻¹⟩
instance : SMul ℕ (Element n c) := ⟨fun k a => ⟨(k : ℚ) • a.coeff⟩⟩
instance : SMul ℤ (Element n c) := ⟨fun k a => ⟨(k : ℚ) • a.coeff⟩⟩
instance : SMul ℚ≥0 (Element n c) := ⟨fun k a => ⟨(k : ℚ) • a.coeff⟩⟩
instance : SMul ℚ (Element n c) := ⟨fun k a => ⟨k • a.coeff⟩⟩
instance : Pow (Element n c) ℕ := ⟨fun a k => ⟨EncodedNumberField.materializedPow c a.coeff k⟩⟩
instance : Pow (Element n c) ℤ := ⟨fun a k => match k with
  | .ofNat k => a ^ k
  | .negSucc k => (a ^ (k + 1))⁻¹⟩
instance : NatCast (Element n c) := ⟨fun k => ⟨(k : ℚ) • EncodedNumberField.one n⟩⟩
instance : IntCast (Element n c) := ⟨fun k => ⟨(k : ℚ) • EncodedNumberField.one n⟩⟩
instance : NNRatCast (Element n c) := ⟨fun k => ⟨(k : ℚ) • EncodedNumberField.one n⟩⟩
instance : RatCast (Element n c) := ⟨fun k => ⟨k • EncodedNumberField.one n⟩⟩

/-- An actual power-basis model of the runtime data, not an arithmetic-law oracle. -/
structure Model (n : ℕ) (c : CoeffVector n) where
  K : Type
  field : Field K
  algebra : Algebra ℚ K
  generator : K
  basis : Module.Basis (Fin n) ℚ K
  basis_eq_pow : ∀ i, basis i = generator ^ i.val
  relation : generator ^ n = interpret generator c

attribute [instance] Model.field Model.algebra

namespace Model
variable (M : Model n c)

def powerBasis : PowerBasis ℚ M.K :=
  ⟨M.generator, n, M.basis, M.basis_eq_pow⟩

def value (a : Element n c) : M.K := interpret M.generator a.coeff

theorem value_injective : Function.Injective M.value := by
  intro a b h
  apply Element.ext
  exact interpret_injective M.powerBasis h

@[simp] theorem value_zero : M.value 0 = 0 := interpret_zero _
@[simp] theorem value_one : M.value 1 = 1 := interpret_one M.generator (show 0 < n from M.powerBasis.dim_pos)
@[simp] theorem value_add (a b : Element n c) : M.value (a + b) = M.value a + M.value b :=
  interpret_add _ _ _
@[simp] theorem value_neg (a : Element n c) : M.value (-a) = -M.value a := interpret_neg _ _
@[simp] theorem value_sub (a b : Element n c) : M.value (a - b) = M.value a - M.value b := by
  change M.value (a + -b) = _
  rw [value_add, value_neg, sub_eq_add_neg]
@[simp] theorem value_mul (a b : Element n c) : M.value (a * b) = M.value a * M.value b :=
  by
    change interpret M.generator (materializedMul c a.coeff b.coeff) = _
    rw [materializedMul_eq]
    exact interpret_mul _ _ _ _ M.relation
@[simp] theorem value_inv (a : Element n c) : M.value a⁻¹ = (M.value a)⁻¹ :=
  by
    change interpret M.generator (materializedInverse c a.coeff) = _
    rw [materializedInverse_eq]
    exact interpret_inverse M.powerBasis _ _ M.relation
@[simp] theorem value_div (a b : Element n c) : M.value (a / b) = M.value a / M.value b := by
  change M.value (a * b⁻¹) = _
  rw [value_mul, value_inv, div_eq_mul_inv]
@[simp] theorem value_pow (a : Element n c) (k : ℕ) : M.value (a ^ k) = M.value a ^ k :=
  by
    change interpret M.generator (materializedPow c a.coeff k) = _
    rw [materializedPow_eq]
    exact interpret_pow _ _ _ M.powerBasis.dim_pos M.relation k
@[simp] theorem value_zpow (a : Element n c) (k : ℤ) : M.value (a ^ k) = M.value a ^ k := by
  cases k with
  | ofNat k => exact (M.value_pow a k).trans (zpow_natCast _ _).symm
  | negSucc k =>
    change M.value ((a ^ (k + 1 : ℕ))⁻¹) = _
    rw [value_inv, value_pow, zpow_negSucc]

@[simp] theorem value_nsmul (k : ℕ) (a : Element n c) : M.value (k • a) = k • M.value a := by
  change interpret M.generator ((k : ℚ) • a.coeff) = _
  rw [interpret_smul]
  simp [value, nsmul_eq_mul]
@[simp] theorem value_zsmul (k : ℤ) (a : Element n c) : M.value (k • a) = k • M.value a := by
  change interpret M.generator ((k : ℚ) • a.coeff) = _
  rw [interpret_smul]
  simp [value, zsmul_eq_mul]
@[simp] theorem value_nnqsmul (k : ℚ≥0) (a : Element n c) : M.value (k • a) = k • M.value a := by
  change interpret M.generator ((k : ℚ) • a.coeff) = _
  rw [interpret_smul]
  simp [value, NNRat.smul_def]
@[simp] theorem value_qsmul (k : ℚ) (a : Element n c) : M.value (k • a) = (k : M.K) * M.value a := by
  change interpret M.generator (k • a.coeff) = _
  rw [interpret_smul]
  simp [value]
@[simp] theorem value_natCast (k : ℕ) : M.value k = k := by
  change interpret M.generator ((k : ℚ) • EncodedNumberField.one n) = _
  rw [interpret_smul, interpret_one M.generator (show 0 < n from M.powerBasis.dim_pos)]
  simp
@[simp] theorem value_intCast (k : ℤ) : M.value k = k := by
  change interpret M.generator ((k : ℚ) • EncodedNumberField.one n) = _
  rw [interpret_smul, interpret_one M.generator (show 0 < n from M.powerBasis.dim_pos)]
  simp
@[simp] theorem value_nnratCast (k : ℚ≥0) : M.value k = k := by
  change interpret M.generator ((k : ℚ) • EncodedNumberField.one n) = _
  rw [interpret_smul, interpret_one M.generator (show 0 < n from M.powerBasis.dim_pos)]
  simp
@[simp] theorem value_ratCast (k : ℚ) : M.value k = k := by
  change interpret M.generator (k • EncodedNumberField.one n) = _
  rw [interpret_smul, interpret_one M.generator (show 0 < n from M.powerBasis.dim_pos)]
  simp

/-- Pull back only the field laws; every data-valued method was fixed above. -/
def fieldStructure : Field (Element n c) :=
  Function.Injective.field M.value M.value_injective M.value_zero M.value_one
    M.value_add M.value_mul M.value_neg M.value_sub M.value_inv M.value_div
    M.value_nsmul M.value_zsmul M.value_nnqsmul
    (fun q x => by rw [Rat.smul_def]; exact M.value_qsmul q x) M.value_pow M.value_zpow
    M.value_natCast M.value_intCast M.value_nnratCast M.value_ratCast
end Model
/-- Semantic validity contains an actual power-basis model. It is a proposition,
so no generator, abstract field, or basis is an input to the runtime methods. -/
def Valid (n : ℕ) (c : CoeffVector n) : Prop := Nonempty (Model n c)

/-- A field dictionary with exclusively runtime rational-vector methods.
The existence of a power-basis model is used only in proof-valued law fields. -/
instance instField [Fact (Valid n c)] : Field (Element n c) where
  add := (· + ·)
  zero := 0
  nsmul := (· • ·)
  mul := (· * ·)
  one := 1
  natCast := Nat.cast
  npow := fun k a => a ^ k
  neg := Neg.neg
  sub := (· - ·)
  zsmul := (· • ·)
  intCast := Int.cast
  inv := Inv.inv
  div := (· / ·)
  zpow := fun k a => a ^ k
  nnratCast := NNRat.cast
  ratCast := Rat.cast
  nnqsmul := (· • ·)
  qsmul := (· • ·)
  add_assoc := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.add_assoc
  zero_add := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.zero_add
  add_zero := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.add_zero
  nsmul_zero := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.nsmul_zero
  nsmul_succ := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.nsmul_succ
  add_comm := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.add_comm
  left_distrib := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.left_distrib
  right_distrib := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.right_distrib
  zero_mul := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.zero_mul
  mul_zero := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.mul_zero
  mul_assoc := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.mul_assoc
  one_mul := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.one_mul
  mul_one := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.mul_one
  natCast_zero := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.natCast_zero
  natCast_succ := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.natCast_succ
  npow_zero := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.npow_zero
  npow_succ := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.npow_succ
  sub_eq_add_neg := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.sub_eq_add_neg
  zsmul_zero' := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.zsmul_zero'
  zsmul_succ' := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.zsmul_succ'
  zsmul_neg' := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.zsmul_neg'
  neg_add_cancel := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.neg_add_cancel
  intCast_ofNat := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.intCast_ofNat
  intCast_negSucc := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.intCast_negSucc
  mul_comm := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.mul_comm
  div_eq_mul_inv := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.div_eq_mul_inv
  zpow_zero' := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.zpow_zero'
  zpow_succ' := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.zpow_succ'
  zpow_neg' := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.zpow_neg'
  exists_pair_ne := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.exists_pair_ne
  mul_inv_cancel := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.mul_inv_cancel
  inv_zero := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.inv_zero
  nnratCast_def := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.nnratCast_def
  nnqsmul_def := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.nnqsmul_def
  ratCast_def := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.ratCast_def
  qsmul_def := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    exact M.fieldStructure.qsmul_def
/-- Any genuine power basis and its checked monic relation prove validity. -/
theorem valid_of_powerBasis {K : Type} [Field K] [Algebra ℚ K]
    (pb : PowerBasis ℚ K) (c : CoeffVector pb.dim)
    (hc : pb.gen ^ pb.dim = interpret pb.gen c) : Valid pb.dim c :=
  ⟨⟨K, inferInstance, inferInstance, pb.gen, pb.basis, pb.basis_eq_pow, hc⟩⟩

instance instCharZero [Fact (Valid n c)] : CharZero (Element n c) where
  cast_injective := by
    obtain ⟨M⟩ := (Fact.out : Valid n c)
    intro a b hab
    apply Nat.cast_injective (R := ℚ)
    apply (algebraMap ℚ M.K).injective
    simpa only [map_natCast, Model.value_natCast] using congrArg M.value hab

/-- Coordinate storage is an explicit rational linear equivalence. -/
def coeffLinearEquiv [Fact (Valid n c)] : Element n c ≃ₗ[ℚ] CoeffVector n where
  toFun := coeff
  invFun := Element.mk
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Finite dimensionality is proved from the finite runtime coordinate space. -/
instance instNumberField [Fact (Valid n c)] : NumberField (Element n c) where
  to_charZero := inferInstance
  to_finiteDimensional := Module.Finite.equiv (coeffLinearEquiv (n := n) (c := c)).symm

/-- Rational polynomial interpretation commutes with a true complex embedding. -/
theorem map_interpret_complex {K : Type} [Field K] [Algebra ℚ K]
    (e : K →+* ℂ) (α : K) (a : CoeffVector n) :
    e (interpret α a) = interpret (e α) a := by
  simp [interpret]

/-- Validity of a supplied conjugate-generator vector, witnessed by an actual
field embedding into the complex numbers. It contains no star-ring law assumption. -/
def StarValid (n : ℕ) (c b : CoeffVector n) : Prop :=
  ∃ (M : Model n c) (e : M.K →+* ℂ),
    interpret (e M.generator) b = star (e M.generator)

/-- Runtime complex conjugation, by finite rational polynomial substitution. -/
def conjugate (b : CoeffVector n) (a : Element n c) : Element n c :=
  ⟨substitute c b a.coeff⟩

theorem conjugation_value (M : Model n c) (e : M.K →+* ℂ) (b : CoeffVector n)
    (hb : interpret (e M.generator) b = star (e M.generator)) (a : Element n c) :
    e (M.value (conjugate b a)) = star (e (M.value a)) := by
  have hc : (e M.generator) ^ n = interpret (e M.generator) c := by
    rw [← map_pow, M.relation, map_interpret_complex]
  change e (interpret M.generator (substitute c b a.coeff)) =
    star (e (interpret M.generator a.coeff))
  rw [map_interpret_complex, map_interpret_complex,
    interpret_conjugate _ c b a.coeff (show 0 < n from M.powerBasis.dim_pos) hc hb]

/-- The star dictionary computes with b alone; model and embedding witnesses occur
only in its law proofs. Install this explicitly for the selected conjugation data. -/
def starRing [Fact (Valid n c)] (b : CoeffVector n) (hb : StarValid n c b) :
    StarRing (Element n c) where
  star := conjugate b
  star_involutive := by
    obtain ⟨M,e,hbe⟩ := hb
    intro a
    apply e.injective.comp M.value_injective
    change e (M.value (conjugate b (conjugate b a))) = e (M.value a)
    rw [conjugation_value M e b hbe, conjugation_value M e b hbe, star_star]
  star_mul := by
    obtain ⟨M,e,hbe⟩ := hb
    intro a d
    apply e.injective.comp M.value_injective
    change e (M.value (conjugate b (a * d))) =
      e (M.value (conjugate b d * conjugate b a))
    simp only [conjugation_value M e b hbe, Model.value_mul, map_mul, star_mul]
  star_add := by
    obtain ⟨M,e,hbe⟩ := hb
    intro a d
    apply e.injective.comp M.value_injective
    change e (M.value (conjugate b (a + d))) =
      e (M.value (conjugate b a + conjugate b d))
    simp only [conjugation_value M e b hbe, Model.value_add, map_add, star_add]

end Element
end ComplexCSP.EncodedNumberField
