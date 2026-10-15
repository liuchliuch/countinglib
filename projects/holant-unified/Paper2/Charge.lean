import Paper2.Network
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

/-!
# Charge and Hamming layers (paper 2, Section 2.10)

The underlying port type is arbitrary and finite. `halfCharge` uses integer
Hamming weight minus half the arity; statements identifying twice this value
with doubled charge explicitly require even arity. No realizability or
complexity assertions are hidden in the support predicates below.
-/

set_option backward.isDefEq.respectTransparency false

namespace Paper2

open scoped BigOperators

variable {ι κ K : Type*}

/-- The number of occupied ports. -/
def weight [Fintype ι] (x : ι → Bool) : ℕ := ∑ i, if x i then 1 else 0

/-- Twice the physical charge: number of ones minus number of zeroes. -/
def doubledCharge [Fintype ι] (x : ι → Bool) : ℤ :=
  2 * (weight x : ℤ) - Fintype.card ι

/-- Integer half-charge, used only at even arity in the paper. -/
def halfCharge [Fintype ι] (x : ι → Bool) : ℤ :=
  (weight x : ℤ) - (Fintype.card ι / 2 : ℕ)

@[simp] theorem weight_false [Fintype ι] : weight (fun _ : ι => false) = 0 := by
  simp [weight]

@[simp] theorem weight_true [Fintype ι] :
    weight (fun _ : ι => true) = Fintype.card ι := by
  simp [weight]

theorem weight_le_card [Fintype ι] (x : ι → Bool) : weight x ≤ Fintype.card ι := by
  calc
    weight x ≤ ∑ _ : ι, 1 := Finset.sum_le_sum (fun i _ => by cases x i <;> simp)
    _ = Fintype.card ι := by simp

theorem weight_eq_zero_iff [Fintype ι] (x : ι → Bool) :
    weight x = 0 ↔ x = fun _ => false := by
  constructor
  · intro h
    funext i
    have hi : (if x i then 1 else 0) ≤ weight x := by
      unfold weight
      exact Finset.single_le_sum (f := fun j => if x j then (1 : ℕ) else 0) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    cases hx : x i <;> simp_all
  · rintro rfl
    exact weight_false

theorem weight_complement_add [Fintype ι] (x : ι → Bool) :
    weight (fun i => !(x i)) + weight x = Fintype.card ι := by
  rw [weight, weight, ← Finset.sum_add_distrib]
  trans ∑ _ : ι, 1
  · apply Finset.sum_congr rfl
    intro i _
    cases x i <;> rfl
  · simp

theorem weight_eq_card_iff [Fintype ι] (x : ι → Bool) :
    weight x = Fintype.card ι ↔ x = fun _ => true := by
  constructor
  · intro h
    have hc : weight (fun i => !(x i)) = 0 := by
      have := weight_complement_add x
      omega
    have he := (weight_eq_zero_iff _).mp hc
    funext i
    have hi := congrFun he i
    cases hx : x i <;> simp_all
  · rintro rfl
    exact weight_true

theorem weight_reindex [Fintype ι] [Fintype κ] (e : ι ≃ κ) (x : κ → Bool) :
    weight (fun i => x (e i)) = weight x := by
  exact Equiv.sum_comp e (fun i => if x i then (1 : ℕ) else 0)

theorem doubledCharge_reindex [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : κ → Bool) :
    doubledCharge (fun i => x (e i)) = doubledCharge x := by
  simp [doubledCharge, weight_reindex, Fintype.card_congr e]

theorem halfCharge_reindex [Fintype ι] [Fintype κ]
    (e : ι ≃ κ) (x : κ → Bool) :
    halfCharge (fun i => x (e i)) = halfCharge x := by
  simp [halfCharge, weight_reindex, Fintype.card_congr e]

theorem doubledCharge_complement [Fintype ι] (x : ι → Bool) :
    doubledCharge (fun i => !(x i)) = -doubledCharge x := by
  have := weight_complement_add x
  unfold doubledCharge
  omega

theorem twice_halfCharge [Fintype ι] (heven : Even (Fintype.card ι))
    (x : ι → Bool) : 2 * halfCharge x = doubledCharge x := by
  obtain ⟨r, hr⟩ := heven
  unfold halfCharge doubledCharge
  omega

theorem halfCharge_complement [Fintype ι] (heven : Even (Fintype.card ι))
    (x : ι → Bool) : halfCharge (fun i => !(x i)) = -halfCharge x := by
  have h₁ := twice_halfCharge heven x
  have h₂ := twice_halfCharge heven (fun i => !(x i))
  rw [doubledCharge_complement] at h₂
  omega

@[simp] theorem halfCharge_false (d : ℕ) :
    halfCharge (fun _ : Fin (2 * d) => false) = -(d : ℤ) := by
  simp [halfCharge]

@[simp] theorem halfCharge_true (d : ℕ) :
    halfCharge (fun _ : Fin (2 * d) => true) = (d : ℤ) := by
  simp [halfCharge] <;> omega

theorem halfCharge_bounds {d : ℕ} (x : Fin (2 * d) → Bool) :
    -(d : ℤ) ≤ halfCharge x ∧ halfCharge x ≤ (d : ℤ) := by
  have := weight_le_card x
  simp only [Fintype.card_fin] at this
  simp only [halfCharge, Fintype.card_fin]
  omega

theorem halfCharge_eq_neg_height_iff {d : ℕ} (x : Fin (2 * d) → Bool) :
    halfCharge x = -(d : ℤ) ↔ x = fun _ => false := by
  rw [← weight_eq_zero_iff]
  simp only [halfCharge, Fintype.card_fin]
  omega

theorem halfCharge_eq_height_iff {d : ℕ} (x : Fin (2 * d) → Bool) :
    halfCharge x = (d : ℤ) ↔ x = fun _ => true := by
  rw [← weight_eq_card_iff]
  simp only [halfCharge, Fintype.card_fin]
  omega

theorem halfCharge_eq_zero_iff {d : ℕ} (x : Fin (2 * d) → Bool) :
    halfCharge x = 0 ↔ weight x = d := by
  simp only [halfCharge, Fintype.card_fin]
  omega

theorem doubledCharge_eq_zero_iff [Fintype ι] (x : ι → Bool) :
    doubledCharge x = 0 ↔ 2 * weight x = Fintype.card ι := by
  unfold doubledCharge
  omega

theorem weight_sum [Fintype ι] [Fintype κ] (x : ι → Bool) (y : κ → Bool) :
    weight (Sum.elim x y) = weight x + weight y := by
  simp only [weight, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]

theorem doubledCharge_sum [Fintype ι] [Fintype κ]
    (x : ι → Bool) (y : κ → Bool) :
    doubledCharge (Sum.elim x y) = doubledCharge x + doubledCharge y := by
  simp only [doubledCharge, weight_sum, Fintype.card_sum, Nat.cast_add]
  ring

theorem halfCharge_sum [Fintype ι] [Fintype κ]
    (hι : Even (Fintype.card ι)) (hκ : Even (Fintype.card κ))
    (x : ι → Bool) (y : κ → Bool) :
    halfCharge (Sum.elim x y) = halfCharge x + halfCharge y := by
  obtain ⟨a, ha⟩ := hι
  obtain ⟨b, hb⟩ := hκ
  simp only [halfCharge, weight_sum, Fintype.card_sum, Nat.cast_add]
  omega

/-- Adding an internal disequality edge adds one zero and one one. -/
theorem weight_X_pair [Fintype ι] (x : ι → Bool) (b : Bool) :
    weight (Sum.elim x (fun c : Bool => if c then !b else b)) = weight x + 1 := by
  rw [weight_sum]
  cases b <;> simp [weight, Fintype.sum_bool]

theorem doubledCharge_X_pair [Fintype ι] (x : ι → Bool) (b : Bool) :
    doubledCharge (Sum.elim x (fun c : Bool => if c then !b else b)) =
      doubledCharge x := by
  simp only [doubledCharge, weight_X_pair, Fintype.card_sum, Fintype.card_bool]
  push_cast
  ring

theorem halfCharge_X_pair [Fintype ι] (x : ι → Bool) (b : Bool) :
    halfCharge (Sum.elim x (fun c : Bool => if c then !b else b)) =
      halfCharge x := by
  simp only [halfCharge, weight_X_pair, Fintype.card_sum, Fintype.card_bool]
  omega

/-- The integer charge is the sum of the individual port signs. -/
theorem doubledCharge_eq_sum [Fintype ι] (x : ι → Bool) :
    doubledCharge x = ∑ i, (if x i then (1 : ℤ) else -1) := by
  have hbit : ∀ b : Bool, (if b then (1 : ℤ) else -1) =
      2 * (if b then (1 : ℤ) else 0) - 1 := by
    intro b
    cases b <;> norm_num
  simp only [hbit, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp [doubledCharge, weight]

namespace NetworkShape

/-- Incidence-bijection conservation, including external ports and loops. -/
theorem sum_doubledCharge_eq_external {n : ℕ} (s : NetworkShape n)
    (x : Fin n → Bool) (z : (Fin s.edges × Bool) → Bool)
    (hX : ∀ e, z (e, false) ≠ z (e, true)) :
    (∑ v, doubledCharge (s.assignment x z v)) = doubledCharge x := by
  simp only [doubledCharge_eq_sum]
  change (∑ v, ∑ i, if Sum.elim x z (s.ports ⟨v, i⟩) then (1 : ℤ) else -1) =
    ∑ i, if x i then (1 : ℤ) else -1
  rw [← Fintype.sum_sigma (fun p : Σ v : Fin s.vertices, Fin (s.arity v) =>
    if Sum.elim x z (s.ports p) then (1 : ℤ) else -1)]
  rw [Equiv.sum_comp s.ports (fun p => if Sum.elim x z p then (1 : ℤ) else -1)]
  rw [Fintype.sum_sum_type, Fintype.sum_prod_type]
  have hedge : ∀ e : Fin s.edges,
      (∑ b : Bool, if z (e, b) then (1 : ℤ) else -1) = 0 := by
    intro e
    have he := hX e
    cases h₀ : z (e, false) <;> cases h₁ : z (e, true) <;>
      simp_all [Fintype.sum_bool]
  simp only [Sum.elim_inl, Sum.elim_inr, hedge, Finset.sum_const_zero, add_zero]

end NetworkShape

namespace Tensor

/-- Support is confined to one doubled-charge layer. -/
def ChargeLayer [Fintype ι] [Zero K] (f : Tensor K ι) (c : ℤ) : Prop :=
  ∀ x, f x ≠ 0 → doubledCharge x = c

/-- Every supported integer half-charge is a multiple of `d`. -/
def HalfChargeDivisible [Fintype ι] [Zero K] (f : Tensor K ι) (d : ℤ) : Prop :=
  ∀ x, f x ≠ 0 → d ∣ halfCharge x

/-- An explicit native-X self-loop on the two distinguished `Bool` ports. -/
def contractX [AddCommMonoid K] (f : Tensor K (ι ⊕ Bool)) : Tensor K ι :=
  fun x => ∑ b : Bool, f (Sum.elim x (fun c : Bool => if c then !b else b))

theorem contractX_chargeLayer [Fintype ι] [AddCommMonoid K]
    {f : Tensor K (ι ⊕ Bool)} {c : ℤ} (hf : ChargeLayer f c) :
    ChargeLayer (contractX f) c := by
  intro x hx
  by_contra h
  apply hx
  apply Finset.sum_eq_zero
  intro b _
  by_contra hb
  exact h (by simpa only [doubledCharge_X_pair] using hf _ hb)

theorem contractX_halfChargeDivisible [Fintype ι] [AddCommMonoid K]
    {f : Tensor K (ι ⊕ Bool)} {d : ℤ} (hf : HalfChargeDivisible f d) :
    HalfChargeDivisible (contractX f) d := by
  intro x hx
  by_contra h
  apply hx
  apply Finset.sum_eq_zero
  intro b _
  by_contra hb
  exact h (by simpa only [halfCharge_X_pair] using hf _ hb)

/-- Tensor products add supported doubled-charge layers. -/
theorem tensor_chargeLayer [Fintype ι] [Fintype κ] [MulZeroClass K]
    {f : Tensor K ι} {g : Tensor K κ} {a b : ℤ}
    (hf : ChargeLayer f a) (hg : ChargeLayer g b) :
    ChargeLayer (tensor f g) (a + b) := by
  intro x hx
  have hf' := hf (fun i => x (.inl i)) (left_ne_zero_of_mul hx)
  have hg' := hg (fun i => x (.inr i)) (right_ne_zero_of_mul hx)
  have he : Sum.elim (fun i => x (.inl i)) (fun i => x (.inr i)) = x := by
    funext i
    cases i <;> rfl
  rw [← hf', ← hg', ← doubledCharge_sum, he]

/-- Reindexing does not change the support's doubled-charge layer. -/
theorem reindex_chargeLayer [Fintype ι] [Fintype κ] [Zero K]
    (e : ι ≃ κ) {f : Tensor K ι} {c : ℤ} (hf : ChargeLayer f c) :
    ChargeLayer (reindex e f) c := by
  intro x hx
  simpa only [doubledCharge_reindex] using hf _ hx

/-- Half-charge divisibility is invariant under port bijections. -/
theorem reindex_halfChargeDivisible [Fintype ι] [Fintype κ] [Zero K]
    (e : ι ≃ κ) {f : Tensor K ι} {d : ℤ} (hf : HalfChargeDivisible f d) :
    HalfChargeDivisible (reindex e f) d := by
  intro x hx
  simpa only [halfCharge_reindex] using hf _ hx

/-- Even tensor factors add half-charges; hence their common divisibility survives. -/
theorem tensor_halfChargeDivisible [Fintype ι] [Fintype κ] [MulZeroClass K]
    (hι : Even (Fintype.card ι)) (hκ : Even (Fintype.card κ))
    {f : Tensor K ι} {g : Tensor K κ} {d : ℤ}
    (hf : HalfChargeDivisible f d) (hg : HalfChargeDivisible g d) :
    HalfChargeDivisible (tensor f g) d := by
  intro x hx
  have hf' := hf (fun i => x (.inl i)) (left_ne_zero_of_mul hx)
  have hg' := hg (fun i => x (.inr i)) (right_ne_zero_of_mul hx)
  have he : Sum.elim (fun i => x (.inl i)) (fun i => x (.inr i)) = x := by
    funext i
    cases i <;> rfl
  have hc := halfCharge_sum hι hκ (fun i => x (.inl i)) (fun i => x (.inr i))
  rw [he] at hc
  rw [hc]
  exact dvd_add hf' hg'

end Tensor

namespace Signature

variable [Semiring K] {n : ℕ}

theorem weight_cons (b : Bool) (x : Fin n → Bool) :
    weight (Fin.cons b x) = (if b then 1 else 0) + weight x := by
  simp only [weight, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]

@[simp] theorem doubledCharge_cons_opposite (b : Bool) (x : Fin n → Bool) :
    doubledCharge (Fin.cons b (Fin.cons (!b) x)) = doubledCharge x := by
  simp only [doubledCharge, weight_cons, Fintype.card_fin]
  cases b <;> simp <;> omega

@[simp] theorem halfCharge_cons_opposite (b : Bool) (x : Fin n → Bool) :
    halfCharge (Fin.cons b (Fin.cons (!b) x)) = halfCharge x := by
  simp only [halfCharge, weight_cons, Fintype.card_fin]
  cases b <;> simp <;> omega

/-- The existing ordered-port contraction has the same conservation property. -/
theorem contract_disequality_chargeLayer {f : Signature K (n + 2)} {c : ℤ}
    (hf : Tensor.ChargeLayer f c) :
    Tensor.ChargeLayer (contract disequality f) c := by
  intro x hx
  rw [contract_disequality] at hx
  by_contra hbad
  have h₀ : f (Fin.cons false (Fin.cons true x)) = 0 := by
    by_contra h
    exact hbad (by simpa only [← Bool.not_false, doubledCharge_cons_opposite] using hf _ h)
  have h₁ : f (Fin.cons true (Fin.cons false x)) = 0 := by
    by_contra h
    exact hbad (by simpa only [← Bool.not_true, doubledCharge_cons_opposite] using hf _ h)
  exact hx (by simp [h₀, h₁])

theorem contract_disequality_halfChargeDivisible {f : Signature K (n + 2)} {d : ℤ}
    (hf : Tensor.HalfChargeDivisible f d) :
    Tensor.HalfChargeDivisible (contract disequality f) d := by
  intro x hx
  rw [contract_disequality] at hx
  by_contra hbad
  have h₀ : f (Fin.cons false (Fin.cons true x)) = 0 := by
    by_contra h
    exact hbad (by simpa only [← Bool.not_false, halfCharge_cons_opposite] using hf _ h)
  have h₁ : f (Fin.cons true (Fin.cons false x)) = 0 := by
    by_contra h
    exact hbad (by simpa only [← Bool.not_true, halfCharge_cons_opposite] using hf _ h)
  exact hx (by simp [h₀, h₁])

end Signature

namespace Network

variable [CommSemiring K] {n : ℕ}

/-- One genuine summand of an open network's denotation. -/
def assignmentTerm (N : Network K n) (x : Fin n → Bool)
    (z : (Fin N.shape.edges × Bool) → Bool) : K :=
  (∏ v, N.vertex v (N.shape.assignment x z v)) *
    ∏ e, N.edge e (z (e, false)) (z (e, true))

theorem vertex_ne_zero_of_term (N : Network K n) (x : Fin n → Bool)
    (z : (Fin N.shape.edges × Bool) → Bool) (h : N.assignmentTerm x z ≠ 0)
    (v : Fin N.shape.vertices) : N.vertex v (N.shape.assignment x z v) ≠ 0 := by
  intro hv
  have hp : (∏ w, N.vertex w (N.shape.assignment x z w)) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ v) hv
  exact h (by simp [assignmentTerm, hp])

theorem edge_ne_zero_of_term (N : Network K n) (x : Fin n → Bool)
    (z : (Fin N.shape.edges × Bool) → Bool) (h : N.assignmentTerm x z ≠ 0)
    (e : Fin N.shape.edges) : N.edge e (z (e, false)) (z (e, true)) ≠ 0 := by
  intro he
  have hp : (∏ j, N.edge j (z (j, false)) (z (j, true))) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ e) he
  exact h (by simp [assignmentTerm, hp])

/-- Each nonzero native-X summand conserves the total external charge. -/
theorem sum_doubledCharge_eq_external_of_term (N : Network K n)
    (hX : ∀ e, N.edge e = Signature.disequality)
    (x : Fin n → Bool) (z : (Fin N.shape.edges × Bool) → Bool)
    (h : N.assignmentTerm x z ≠ 0) :
    (∑ v, doubledCharge (N.shape.assignment x z v)) = doubledCharge x := by
  apply N.shape.sum_doubledCharge_eq_external
  intro e he
  have hn := N.edge_ne_zero_of_term x z h e
  rw [hX e] at hn
  exact hn (by simp [Signature.disequality, he])

/-- A fixed gadget built from single-charge-layer vertices is itself on one
charge layer. Cancellation can remove support but cannot introduce new charge. -/
theorem denote_chargeLayer (N : Network K n)
    (hX : ∀ e, N.edge e = Signature.disequality)
    (c : Fin N.shape.vertices → ℤ)
    (hc : ∀ v, Tensor.ChargeLayer (N.vertex v) (c v)) :
    Tensor.ChargeLayer N.denote (∑ v, c v) := by
  intro x hx
  by_contra hbad
  apply hx
  change (∑ z, N.assignmentTerm x z) = 0
  apply Finset.sum_eq_zero
  intro z _
  by_contra hz
  have hcon := N.sum_doubledCharge_eq_external_of_term hX x z hz
  have hv : ∀ v, doubledCharge (N.shape.assignment x z v) = c v := by
    intro v
    exact hc v _ (N.vertex_ne_zero_of_term x z hz v)
  apply hbad
  simpa only [hv] using hcon.symm

/-- The all-even form of the same conservation identity. -/
theorem sum_halfCharge_eq_external_of_term (N : Network K n)
    (hn : Even n) (hlocal : ∀ v, Even (N.shape.arity v))
    (hX : ∀ e, N.edge e = Signature.disequality)
    (x : Fin n → Bool) (z : (Fin N.shape.edges × Bool) → Bool)
    (h : N.assignmentTerm x z ≠ 0) :
    (∑ v, halfCharge (N.shape.assignment x z v)) = halfCharge x := by
  have hcon := N.sum_doubledCharge_eq_external_of_term hX x z h
  have hv : ∀ v, doubledCharge (N.shape.assignment x z v) =
      2 * halfCharge (N.shape.assignment x z v) := by
    intro v
    exact (twice_halfCharge (by simpa using hlocal v) _).symm
  rw [← twice_halfCharge (by simpa using hn) x] at hcon
  simp only [hv, ← Finset.mul_sum] at hcon
  omega

/-- Divisibility of all local half-charges is inherited by every even-arity
native-X network output, irrespective of cancellation in its sum. -/
theorem denote_halfChargeDivisible (N : Network K n)
    (hn : Even n) (hlocal : ∀ v, Even (N.shape.arity v))
    (hX : ∀ e, N.edge e = Signature.disequality) (d : ℤ)
    (hd : ∀ v, Tensor.HalfChargeDivisible (N.vertex v) d) :
    Tensor.HalfChargeDivisible N.denote d := by
  intro x hx
  by_contra hbad
  apply hx
  change (∑ z, N.assignmentTerm x z) = 0
  apply Finset.sum_eq_zero
  intro z _
  by_contra hz
  apply hbad
  rw [← N.sum_halfCharge_eq_external_of_term hn hlocal hX x z hz]
  apply Finset.dvd_sum
  intro v _
  exact hd v _ (N.vertex_ne_zero_of_term x z hz v)

end Network
end Paper2

