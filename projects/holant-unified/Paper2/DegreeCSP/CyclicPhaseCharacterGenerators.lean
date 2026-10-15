import Paper2.Tractable.Affine
import Paper2.DegreeCSP.CyclicPhaseCharacter
import Mathlib.Algebra.Group.Subgroup.Ker

/-! Cycle relations define an actual character of the generated residue subgroup. -/
namespace Paper2.DegreeCSP.CyclicPhaseCharacterGenerators
open Tractable
noncomputable section

variable {s k : ℕ}

/-- The natural-exponent relations among the given generators. -/
def CycleRelations (d : Fin s → ℕ) (v : Fin s → AlgebraicComplex) (k : ℕ) : Prop :=
  ∀ a : Fin s → ℕ, k ∣ ∑ i, a i * d i → ∏ i, v i ^ a i = 1

theorem generator_pow (d : Fin s → ℕ) (v : Fin s → AlgebraicComplex)
    (hc : CycleRelations d v k) (i : Fin s) : v i ^ k = 1 := by
  have h := hc (fun j => if j = i then k else 0)
  have hd : k ∣ ∑ j, (if j = i then k else 0) * d j := by
    simpa only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      using dvd_mul_right k (d i)
  have hp : (∏ j, v j ^ (if j = i then k else 0)) = v i ^ k := by
    rw [Finset.prod_eq_single i]
    · simp
    · intro j hj hji
      simp [hji]
    · simp
  exact hp.symm.trans (h hd)

theorem generator_ne_zero (hk : 0 < k) (d : Fin s → ℕ)
    (v : Fin s → AlgebraicComplex) (hc : CycleRelations d v k) (i : Fin s) :
    v i ≠ 0 := by
  intro hz
  have hp := generator_pow d v hc i
  rw [hz, zero_pow (Nat.ne_of_gt hk)] at hp
  exact zero_ne_one hp

/-- A generator as a unit, justified by its actual cycle relation. -/
def generatorUnit (hk : 0 < k) (d : Fin s → ℕ)
    (v : Fin s → AlgebraicComplex) (hc : CycleRelations d v k) (i : Fin s) :
    AlgebraicComplexˣ := Units.mk0 (v i) (generator_ne_zero hk d v hc i)

@[simp] theorem generatorUnit_val (hk : 0 < k) (d : Fin s → ℕ)
    (v : Fin s → AlgebraicComplex) (hc : CycleRelations d v k) (i : Fin s) :
    (generatorUnit hk d v hc i).val = v i := rfl

theorem generatorUnit_pow (hk : 0 < k) (d : Fin s → ℕ)
    (v : Fin s → AlgebraicComplex) (hc : CycleRelations d v k) (i : Fin s) :
    generatorUnit hk d v hc i ^ k = 1 := by
  apply Units.ext
  simpa using generator_pow d v hc i

/-- The degree-weight map on the finite product of residue groups. -/
def weight (d : Fin s → ℕ) (k : ℕ) : (Fin s → ZMod k) →+ ZMod k where
  toFun a := ∑ i, a i * (d i : ZMod k)
  map_zero' := by simp
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]

@[simp] theorem weight_apply (d : Fin s → ℕ) (k : ℕ) (a : Fin s → ZMod k) :
    weight d k a = ∑ i, a i * (d i : ZMod k) := rfl

/-- The literal product of generator powers is a character of the residue product. -/
def phase (hk : 0 < k) (d : Fin s → ℕ)
    (v : Fin s → AlgebraicComplex) (hc : CycleRelations d v k) :
    (Fin s → ZMod k) →+ Additive (AlgebraicComplexˣ) := by
  letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
  refine
    { toFun := fun a => Additive.ofMul (∏ i, generatorUnit hk d v hc i ^ (a i).val)
      map_zero' := by simp
      map_add' := ?_ }
  intro a b
  change (∏ i, generatorUnit hk d v hc i ^ (a i + b i).val) =
    (∏ i, generatorUnit hk d v hc i ^ (a i).val) *
      (∏ i, generatorUnit hk d v hc i ^ (b i).val)
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i hi
  rw [ZMod.val_add, ← pow_eq_pow_mod _ (generatorUnit_pow hk d v hc i), pow_add]

@[simp] theorem phase_apply (hk : 0 < k) (d : Fin s → ℕ)
    (v : Fin s → AlgebraicComplex) (hc : CycleRelations d v k) (a : Fin s → ZMod k) :
    (phase hk d v hc a).toMul = ∏ i, generatorUnit hk d v hc i ^ (a i).val := rfl

theorem weight_ker_le_phase_ker (hk : 0 < k) (d : Fin s → ℕ)
    (v : Fin s → AlgebraicComplex) (hc : CycleRelations d v k) :
    (weight d k).ker ≤ (phase hk d v hc).ker := by
  let : NeZero k := ⟨Nat.ne_of_gt hk⟩
  intro a ha
  have hw : ((∑ i, (a i).val * d i : ℕ) : ZMod k) = 0 := by
    simpa only [Nat.cast_sum, Nat.cast_mul, ZMod.natCast_zmod_val, weight_apply]
      using AddMonoidHom.mem_ker.mp ha
  have hp := hc (fun i => (a i).val) ((ZMod.natCast_eq_zero_iff _ _).mp hw)
  apply AddMonoidHom.mem_ker.mpr
  change Additive.ofMul (∏ i, generatorUnit hk d v hc i ^ (a i).val) = 0
  apply congrArg Additive.ofMul
  apply Units.ext
  simpa using hp

/-- The subgroup reached by the actual degree-weight map. -/
def residueSubgroup (d : Fin s → ℕ) (k : ℕ) : AddSubgroup (ZMod k) := (weight d k).range

/-- Descend the literal generator product through the degree-weight map. -/
def subgroupCharacter (hk : 0 < k) (d : Fin s → ℕ)
    (v : Fin s → AlgebraicComplex) (hc : CycleRelations d v k) :
    residueSubgroup d k →+ Additive (AlgebraicComplexˣ) :=
  (weight d k).rangeRestrict.liftOfSurjective (weight d k).rangeRestrict_surjective
    ⟨phase hk d v hc, by
      simpa only [AddMonoidHom.ker_rangeRestrict] using weight_ker_le_phase_ker hk d v hc⟩

theorem subgroupCharacter_weight (hk : 0 < k) (d : Fin s → ℕ)
    (v : Fin s → AlgebraicComplex) (hc : CycleRelations d v k) (a : Fin s → ZMod k) :
    subgroupCharacter hk d v hc ((weight d k).rangeRestrict a) = phase hk d v hc a := by
  exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

/-- Evaluation on natural residues retains exactly the original coefficients. -/
theorem phase_natural (hk : 0 < k) (d : Fin s → ℕ)
    (v : Fin s → AlgebraicComplex) (hc : CycleRelations d v k) (a : Fin s → ℕ) :
    (phase hk d v hc (fun i => (a i : ZMod k))).toMul.val = ∏ i, v i ^ a i := by
  simp only [phase_apply, Units.coe_prod, Units.val_pow_eq_pow_val, generatorUnit_val,
    ZMod.val_natCast]
  apply Finset.prod_congr rfl
  intro i hi
  exact (pow_eq_pow_mod (a i) (generator_pow d v hc i)).symm

/-- The residue-product vector selecting a single named generator. -/
def basis (i : Fin s) : Fin s → ZMod k := fun j => if j = i then 1 else 0

@[simp] theorem weight_basis (d : Fin s → ℕ) (k : ℕ) (i : Fin s) :
    weight d k (basis i) = (d i : ZMod k) := by
  simp only [weight_apply, basis, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem phase_basis (hk : 0 < k) (d : Fin s → ℕ)
    (v : Fin s → AlgebraicComplex) (hc : CycleRelations d v k) (i : Fin s) :
    (phase hk d v hc (basis i)).toMul.val = v i := by
  have he : basis i = (fun j => ((if j = i then 1 else 0 : ℕ) : ZMod k)) := by
    ext j
    split_ifs <;> simp [basis, *]
  rw [he, phase_natural]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

theorem subgroupCharacter_basis (hk : 0 < k) (d : Fin s → ℕ)
    (v : Fin s → AlgebraicComplex) (hc : CycleRelations d v k) (i : Fin s) :
    (subgroupCharacter hk d v hc ((weight d k).rangeRestrict (basis i))).toMul.val =
      v i := by
  rw [subgroupCharacter_weight, phase_basis]

/-- The actual cycle relations force every generator to be a power of one
`k`-th root in the algebraic-complex field. -/
theorem exists_phase (hk : 0 < k) (d : Fin s → ℕ)
    (v : Fin s → AlgebraicComplex) (hc : CycleRelations d v k) :
    ∃ θ : AlgebraicComplex, θ ^ k = 1 ∧ ∀ i, v i = θ ^ d i := by
  obtain ⟨θ, hθ, hχ⟩ := CyclicPhaseCharacter.extend_character hk
    (residueSubgroup d k) (subgroupCharacter hk d v hc)
  refine ⟨θ, hθ, ?_⟩
  intro i
  have h := hχ ((weight d k).rangeRestrict (basis i))
  rw [subgroupCharacter_basis] at h
  change v i = θ ^ (weight d k (basis i)).val at h
  rw [weight_basis, ZMod.val_natCast] at h
  exact h.trans (pow_eq_pow_mod (d i) hθ).symm

/-- Unbundled form of the finite-generator phase theorem. -/
theorem exists_phase_of_cycles (hk : 0 < k) (d : Fin s → ℕ)
    (v : Fin s → AlgebraicComplex)
    (hcycle : ∀ a : Fin s → ℕ, k ∣ ∑ i, a i * d i → ∏ i, v i ^ a i = 1) :
    ∃ θ : AlgebraicComplex, θ ^ k = 1 ∧ ∀ i, v i = θ ^ d i :=
  exists_phase hk d v hcycle

end
end Paper2.DegreeCSP.CyclicPhaseCharacterGenerators
