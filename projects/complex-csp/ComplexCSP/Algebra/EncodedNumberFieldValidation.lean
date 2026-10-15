import ComplexCSP.Algebra.EncodedNumberFieldElement
import ComplexCSP.Algebra.MonicIrreducibility
import ComplexCSP.Algebra.EffectiveRootsCoefficients
import Mathlib.RingTheory.AdjoinRoot

/-! # Checked monic-tail ingress for the executable coordinate field

A finite integer coefficient checker establishes an actual irreducible quotient
field and power basis. Those semantic constructions occur only in proofs. The
runtime guards and arithmetic use integer and rational vectors exclusively.
-/
set_option backward.isDefEq.respectTransparency false

namespace ComplexCSP.EncodedNumberField
open scoped BigOperators
open Polynomial

namespace Element

/-- A monic irreducible relation gives an actual field model via AdjoinRoot.
The quotient, abstract field operations and basis are confined to this proof. -/
theorem valid_of_monic_irreducible {n : ℕ} (c : CoeffVector n) (p : Polynomial ℚ)
    (hp : p.Monic) (hi : Irreducible p) (hd : p.natDegree = n)
    (hc : ∀ i : Fin n, p.coeff i.val = -c i) : Valid n c := by
  classical
  letI : Fact (Irreducible p) := ⟨hi⟩
  let K := AdjoinRoot p
  let pb := AdjoinRoot.powerBasis hp.ne_zero
  let B : Module.Basis (Fin n) ℚ K := pb.basis.reindex (finCongr hd)
  have hB (i : Fin n) : B i = AdjoinRoot.root p ^ i.val := by
    change (pb.basis.reindex (finCongr hd)) i = _
    rw [Module.Basis.reindex_apply, pb.basis_eq_pow]
    rfl
  have hr : Polynomial.aeval (AdjoinRoot.root p) p = 0 := by
    rw [AdjoinRoot.aeval_eq, AdjoinRoot.mk_self]
  have htop : p.coeff n = 1 := by rw [← hd, hp.coeff_natDegree]
  rw [Polynomial.aeval_eq_sum_range, hd, Finset.sum_range_succ, htop, one_smul] at hr
  simp only [Algebra.smul_def] at hr
  have hpow : AdjoinRoot.root p ^ n = interpret (AdjoinRoot.root p) c := by
    have he := eq_neg_of_add_eq_zero_right hr
    rw [Finset.sum_range] at he
    simp only [hc, map_neg, neg_mul, Finset.sum_neg_distrib, neg_neg] at he
    exact he
  exact ⟨⟨K, inferInstance, inferInstance, AdjoinRoot.root p, B, hB, hpow⟩⟩

/-- Successful finite irreducibility testing discharges the field-model obligation
for the public integer-tail coordinate representation. -/
theorem valid_of_irreducibleMonicTail {n : ℕ} (a : Fin n → ℤ)
    (ha : MonicIrreducibility.irreducibleMonicTail a = true) :
    Valid n (EffectiveRoots.coefficientRelation a) := by
  let p := MonicIrreducibility.denote (MonicIrreducibility.fromTail a)
  have hp : p.Monic := MonicIrreducibility.denote_monic _
    (MonicIrreducibility.fromTail_leading a)
  have hd : p.natDegree = n := MonicIrreducibility.denote_natDegree _
    (MonicIrreducibility.fromTail_leading a)
  apply valid_of_monic_irreducible _ (p.map (Int.castRingHom ℚ))
    (hp.map _) ((MonicIrreducibility.irreducibleMonicTail_correct a).mp ha)
  · rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective, hd]
  · intro i
    simp [p, EffectiveRoots.coefficientRelation, MonicIrreducibility.coefficient,
      MonicIrreducibility.fromTail, i.isLt, show i.val < n + 1 by omega]

end Element

/-- A finite Boolean validation guard, including rejection of degree zero. -/
def validTail {n : ℕ} (a : Fin n → ℤ) : Bool :=
  MonicIrreducibility.irreducibleMonicTail a

theorem validTail_sound {n : ℕ} (a : Fin n → ℤ) (h : validTail a = true) :
    Element.Valid n (EffectiveRoots.coefficientRelation a) :=
  Element.valid_of_irreducibleMonicTail a h

/-- A raw-data entry point: no caller-supplied semantic model is required. -/
def checkedInverse {n : ℕ} (a : Fin n → ℤ) (v : CoeffVector n) : Option (CoeffVector n) :=
  if h : validTail a = true then
    letI : Fact (Element.Valid n (EffectiveRoots.coefficientRelation a)) := ⟨validTail_sound a h⟩
    some (((⟨v⟩ : Element n (EffectiveRoots.coefficientRelation a))⁻¹).coeff)
  else none

@[simp] theorem checkedInverse_of_valid {n : ℕ} (a : Fin n → ℤ) (v : CoeffVector n)
    (h : validTail a = true) :
    checkedInverse a v = some (inverse (EffectiveRoots.coefficientRelation a) v) := by
  simp only [checkedInverse, dif_pos h]
  change some (materializedInverse _ _) = _
  rw [materializedInverse_eq]

@[simp] theorem checkedInverse_of_invalid {n : ℕ} (a : Fin n → ℤ) (v : CoeffVector n)
    (h : validTail a = false) : checkedInverse a v = none := by simp [checkedInverse, h]

end ComplexCSP.EncodedNumberField
