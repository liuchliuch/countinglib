import Paper2.HeightOne.PhaseCards.Source

/-! The native complement relation following source Lemma 5.10, proved from
literal finite Walsh sums rather than treated as a new symmetry assumption. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.PhaseCards
noncomputable section
attribute [local instance] Classical.propDecidable
open Tractable
open scoped BigOperators
variable {ι : Type} [Fintype ι]

lemma walsh_complement_entry (a b : Bool) :
    walsh (!a) b = (-1 : AlgebraicComplex) ^ (if b then 1 else 0) * walsh a b := by
  cases a <;> cases b <;> norm_num [walsh]

lemma walsh_complement_product (x y : ι → Bool) :
    (∏ i, walsh (!(x i)) (y i)) =
      (-1 : AlgebraicComplex) ^ weight y * ∏ i, walsh (x i) (y i) := by
  simp_rw [walsh_complement_entry]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  rfl

lemma action_walsh_complement {g : Tensor AlgebraicComplex ι} {p : ℕ}
    (hg : SupportedOnParity g p) (x : ι → Bool) :
    action walsh g (fun i => !(x i)) = (-1 : AlgebraicComplex) ^ p * action walsh g x := by
  classical
  simp only [action, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  rw [walsh_complement_product]
  by_cases hy : g y = 0
  · simp [hy]
  · have hp : weight y % 2 = p := hg y hy
    rw [neg_one_pow_eq_pow_mod_two, hp]
    ring

/-- A Walsh parity class is a native complement eigenspace with the same sign. -/
theorem complement_of_walsh_supported {f : Tensor AlgebraicComplex ι} {p : ℕ}
    (hf : SupportedOnParity (walshCoordinates f) p) (x : ι → Bool) :
    f (fun i => !(x i)) = (-1 : AlgebraicComplex) ^ p * f x := by
  have h := action_walsh_complement hf x
  simpa only [walsh_action_cancel] using h

theorem complement_of_walsh_hasParity {f : Tensor AlgebraicComplex ι}
    (hf : HasParity (walshCoordinates f)) :
    (∀ x, f (fun i => !(x i)) = f x) ∨ (∀ x, f (fun i => !(x i)) = -f x) := by
  obtain ⟨p, hp, hs⟩ := (hasParity_iff_exists _).mp hf
  have hcases : p = 0 ∨ p = 1 := by omega
  rcases hcases with rfl | rfl
  · left
    intro x
    simpa using complement_of_walsh_supported hs x
  · right
    intro x
    simpa using complement_of_walsh_supported hs x

theorem complement_of_walsh_even {f : Tensor AlgebraicComplex ι}
    (hf : SupportedOnParity (walshCoordinates f) 0) :
    ∀ x, f (fun i => !(x i)) = f x := by
  intro x
  simpa using complement_of_walsh_supported hf x

lemma walshInv_complement_entry (a b : Bool) :
    walshInv a (!b) = (-1 : AlgebraicComplex) ^ (if a then 1 else 0) * walshInv a b := by
  cases a <;> cases b <;> norm_num [walshInv, walsh]

lemma walshCoordinates_input_complement (f : Tensor AlgebraicComplex ι) (x : ι → Bool) :
    walshCoordinates (fun y => f (fun i => !(y i))) x =
      (-1 : AlgebraicComplex) ^ weight x * walshCoordinates f x := by
  classical
  unfold walshCoordinates action
  rw [Finset.mul_sum]
  symm
  apply Fintype.sum_equiv (Equiv.piCongrRight (fun _ : ι => Equiv.boolNot))
  intro y
  change (-1 : AlgebraicComplex) ^ weight x * ((∏ i, walshInv (x i) (y i)) * f y) =
    (∏ i, walshInv (x i) (!(y i))) * f (fun i => !(!(y i)))
  simp only [Bool.not_not]
  have he : (∏ i, walshInv (x i) (!(y i))) =
      (-1 : AlgebraicComplex) ^ weight x * ∏ i, walshInv (x i) (y i) := by
    simp_rw [walshInv_complement_entry]
    rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    rfl
  rw [he, mul_assoc]

lemma walshCoordinates_scale (c : AlgebraicComplex) (f : Tensor AlgebraicComplex ι) :
    walshCoordinates (fun y => c * f y) = fun x => c * walshCoordinates f x := by
  funext x
  simp only [walshCoordinates, action, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

/-- Converse Walsh duality, including zero tensors. -/
theorem walsh_supported_of_complement {f : Tensor AlgebraicComplex ι} {p : ℕ}
    (hp : p < 2) (hf : ∀ x, f (fun i => !(x i)) = (-1 : AlgebraicComplex) ^ p * f x) :
    SupportedOnParity (walshCoordinates f) p := by
  intro x hx
  have h := walshCoordinates_input_complement f x
  have he : (fun y => f (fun i => !(y i))) = (fun y => (-1 : AlgebraicComplex) ^ p * f y) :=
    funext hf
  rw [he, walshCoordinates_scale] at h
  have hs := mul_right_cancel₀ hx h
  rw [neg_one_pow_eq_pow_mod_two (weight x)] at hs
  unfold parity
  have hw : weight x % 2 < 2 := Nat.mod_lt _ (by decide)
  interval_cases p
  · by_contra hn
    have hw1 : weight x % 2 = 1 := by omega
    norm_num [hw1] at hs
  · by_contra hn
    have hw0 : weight x % 2 = 0 := by omega
    norm_num [hw0] at hs

theorem walsh_supported_iff_complement {f : Tensor AlgebraicComplex ι} {p : ℕ} (hp : p < 2) :
    SupportedOnParity (walshCoordinates f) p ↔
      ∀ x, f (fun i => !(x i)) = (-1 : AlgebraicComplex) ^ p * f x :=
  ⟨fun h x => complement_of_walsh_supported h x, walsh_supported_of_complement hp⟩

end
end Paper2.HeightOne.PhaseCards
