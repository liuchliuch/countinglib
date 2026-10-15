import Paper2.HeightOne.Cyclic.ActualDressing
import Paper2.HeightOne.Cyclic.QuaternaryFourier

/-! The shared cyclic RN family and its odd-order phase normalization.
All phases belong to the actual finite root group.  Fourier coordinates are
only used to describe the output of the recorded binary attachments.
-/
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable PhasePencil PhaseCards Dihedral
open scoped BigOperators

def QuaternaryRows (N : ℕ) (p t : AlgebraicComplex)
    (x y : Fin 3 → AlgebraicComplex) : Prop :=
  ∀ i, Relation N p (x i) (y i) t ∧ Relation N p (y i) (x i) t

/-- Precise shared cyclic family with live endpoints.  The same lambda serves
all three complementary pairs, including zero pairs. -/
theorem shared_cyclic_live {N : ℕ} (hN : 0 < N)
    {p t : AlgebraicComplex} {x y : Fin 3 → AlgebraicComplex}
    (hp : p ≠ 0) (h : QuaternaryRows N p t x y) :
    ∃ lambda : AlgebraicComplex, Root N lambda ∧ t = lambda * p ∧
      ∀ i, ∃ alpha : AlgebraicComplex, Root N alpha ∧
        ((x i = 0 ∧ y i = 0) ∨
          (x i = -p * lambda / alpha ∧ y i = -p * alpha)) := by
  obtain ⟨ht, ⟨lambda, hlambda, htlam⟩, _⟩ :=
    paired_relation_live hN hp (h 0).1 (h 0).2
  refine ⟨lambda, hlambda, htlam, ?_⟩
  intro i
  obtain ⟨_, _, hzero | ⟨a, b, ha, hb, hxi, hyi, hti⟩⟩ :=
    paired_relation_live hN hp (h i).1 (h i).2
  · exact ⟨1, by simp [Root], Or.inl hzero⟩
  · refine ⟨b, hb, Or.inr ⟨?_, ?_⟩⟩
    · have hlam : lambda = a * b := (mul_right_cancel₀ hp) (htlam.symm.trans hti)
      rw [hxi, hlam]
      field_simp [root_ne_zero hN hb]
    · rw [hyi]
      ring

/-- Zero endpoints retain a positive phase ratio even for a vanishing pair. -/
theorem shared_cyclic_zero {N : ℕ} (hN : 0 < N)
    {x y : Fin 3 → AlgebraicComplex} (h : QuaternaryRows N 0 0 x y) :
    ∀ i, ∃ alpha : AlgebraicComplex, Root N alpha ∧ y i = alpha * x i :=
  fun i => relation_zero_endpoints hN (h i).1

def rootWeight {N : ℕ} (r : Fin 4 → rootsOfUnity N AlgebraicComplex)
    (x : Fin 4 → Bool) : rootsOfUnity N AlgebraicComplex :=
  ∏ j, if x j then r j else 1

lemma rootWeight_zero {N : ℕ} (r : Fin 4 → rootsOfUnity N AlgebraicComplex) :
    rootWeight r (fun _ => false) = 1 := by simp [rootWeight]

lemma rootWeight_one {N : ℕ} (r : Fin 4 → rootsOfUnity N AlgebraicComplex) :
    rootWeight r (fun _ => true) = (dressingMap r).1 := by simp [rootWeight, dressingMap]

lemma rootWeight_central {N : ℕ} (r : Fin 4 → rootsOfUnity N AlgebraicComplex)
    (i : Fin 3) :
    rootWeight r (centralWord i (fun _ => false)) = (dressingMap r).2 i := by
  fin_cases i <;>
    simp [rootWeight, centralWord, flipPair, dressingMap, Fin.prod_univ_succ, mul_comm]

lemma rootWeight_complement {N : ℕ} (r : Fin 4 → rootsOfUnity N AlgebraicComplex)
    (x : Fin 4 → Bool) :
    rootWeight r (flipAll x) = (dressingMap r).1 / rootWeight r x := by
  have h (j : Fin 4) : (if !(x j) then r j else 1) =
      r j / (if x j then r j else 1) := by cases x j <;> simp
  change (∏ j, if !(x j) then r j else 1) = (∏ j, r j) / (∏ j, if x j then r j else 1)
  simp_rw [h]
  rw [Finset.prod_div_distrib]

lemma coe_rootWeight {N : ℕ} (r : Fin 4 → rootsOfUnity N AlgebraicComplex)
    (x : Fin 4 → Bool) :
    ((rootWeight r x).val : AlgebraicComplex) = ∏ j, if x j then ((r j).val : AlgebraicComplex) else 1 := by
  simp only [rootWeight, Subgroup.val_finsetProd, Units.coe_prod]
  apply Finset.prod_congr rfl
  intro j _
  cases x j <;> rfl

/-- Odd-order dressing realizes an arbitrary common endpoint phase and all
three independent central-pair phases. -/
theorem prescribe_four_port_phases {N : ℕ} (hodd : Odd N)
    (R : rootsOfUnity N AlgebraicComplex)
    (u : Fin 3 → rootsOfUnity N AlgebraicComplex) :
    ∃ r : Fin 4 → rootsOfUnity N AlgebraicComplex,
      rootWeight r (fun _ => true) = R ∧
      (∀ i, rootWeight r (centralWord i (fun _ => false)) = u i) ∧
      (∀ i, rootWeight r (flipAll (centralWord i (fun _ => false))) = R / u i) := by
  obtain ⟨r, hr⟩ := (odd_dressing_bijective hodd).2 (R, u)
  refine ⟨r, ?_, ?_, ?_⟩
  · rw [rootWeight_one, hr]
  · intro i
    rw [rootWeight_central, hr]
  · intro i
    rw [rootWeight_complement, rootWeight_central, hr]

end
end Paper2.HeightOne.Cyclic
