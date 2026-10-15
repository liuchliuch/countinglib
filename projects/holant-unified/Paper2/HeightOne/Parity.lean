import Paper2.EndpointSelfLoop
import Paper2.Kernel
import Paper2.Bell
import Paper2.TensorClosure
import Mathlib.Tactic
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Walsh parity from actual diagonal-plus contractions

The coefficient-table core of paper 2, Lemma 5.10 (source label
`lem:odd-dih-all-arity-parity`). Three distinct phases suffice; the parity of
individual contractions may vary and zero contractions are allowed. Every
contraction below deletes actual distinct ports using `splitPorts`.

The group-membership and prime-factorization bridges are not assumed to have
been constructed here. The main input is the parity of the actual contracted
tables, rather than the parity of the original table or its slices.
-/

set_option linter.unusedSimpArgs false

namespace Paper2.HeightOne

open scoped BigOperators
open EndpointSelfLoop

variable {K : Type*} {ι κ : Type}

/-- Walsh support parity is Hamming weight modulo two. -/
def parity [Fintype ι] (x : ι → Bool) : ℕ := weight x % 2

/-- All nonzero coefficients lie on the stated Walsh parity. -/
def SupportedOnParity [Fintype ι] [Zero K] (f : Tensor K ι) (p : ℕ) : Prop :=
  ∀ x, f x ≠ 0 → parity x = p

/-- Pairwise formulation, so the zero tensor is allowed without choosing a
spurious nonzero coefficient. -/
def HasParity [Fintype ι] [Zero K] (f : Tensor K ι) : Prop :=
  ∀ x y, f x ≠ 0 → f y ≠ 0 → parity x = parity y

 theorem hasParity_iff_exists [Fintype ι] [Zero K] (f : Tensor K ι) :
    HasParity f ↔ ∃ p, p < 2 ∧ SupportedOnParity f p := by
  classical
  constructor
  · intro h
    by_cases hf : ∃ x, f x ≠ 0
    · obtain ⟨x, hx⟩ := hf
      exact ⟨parity x, Nat.mod_lt _ (by omega), fun y hy => h y x hy hx⟩
    · exact ⟨0, by omega, fun x hx => False.elim (hf ⟨x, hx⟩)⟩
  · rintro ⟨p, _, h⟩ x y hx hy
    exact (h x hx).trans (h y hy).symm

 theorem supportedOnParity_hasParity [Fintype ι] [Zero K]
    {f : Tensor K ι} {p : ℕ} (h : SupportedOnParity f p) : HasParity f :=
  fun x y hx hy => (h x hx).trans (h y hy).symm

 theorem hasParity_zero [Fintype ι] [Zero K] : HasParity (0 : Tensor K ι) := by
  intro x y hx
  exact False.elim (hx rfl)

 theorem affine_two_roots [CommRing K] [NoZeroDivisors K]
    {a b s t : K} (hst : s ≠ t) (hs : a - s * b = 0)
    (ht : a - t * b = 0) : a = 0 ∧ b = 0 := by
  have hb : (s - t) * b = 0 := by linear_combination ht - hs
  have hb0 : b = 0 := (mul_eq_zero.mp hb).resolve_left (sub_ne_zero.mpr hst)
  exact ⟨by simpa [hb0] using hs, hb0⟩

 theorem affine_survives_one_of_two [CommRing K] [NoZeroDivisors K]
    {a b s t : K} (hst : s ≠ t) (hab : a ≠ 0 ∨ b ≠ 0) :
    a - s * b ≠ 0 ∨ a - t * b ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨ha, hb⟩ := affine_two_roots hst h.1 h.2
  rcases hab with h | h <;> contradiction

/-- Two nontrivial affine coordinates can each cancel at only one phase.
Three different phases therefore preserve both simultaneously. -/
 theorem affine_two_coordinates_survive [CommRing K] [NoZeroDivisors K]
    (s : Fin 3 → K) (hs : Function.Injective s) {a b c d : K}
    (hab : a ≠ 0 ∨ b ≠ 0) (hcd : c ≠ 0 ∨ d ≠ 0) :
    ∃ j : Fin 3, a - s j * b ≠ 0 ∧ c - s j * d ≠ 0 := by
  have h01 : s 0 ≠ s 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (hs h)
  have h02 : s 0 ≠ s 2 := fun h => (by decide : (0 : Fin 3) ≠ 2) (hs h)
  have h12 : s 1 ≠ s 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (hs h)
  by_cases ha0 : a - s 0 * b = 0
  · have ha1 := (affine_survives_one_of_two h01 hab).resolve_left (not_not_intro ha0)
    have ha2 := (affine_survives_one_of_two h02 hab).resolve_left (not_not_intro ha0)
    rcases affine_survives_one_of_two h12 hcd with hc1 | hc2
    · exact ⟨1, ha1, hc1⟩
    · exact ⟨2, ha2, hc2⟩
  · by_cases hc0 : c - s 0 * d = 0
    · have hc1 := (affine_survives_one_of_two h01 hcd).resolve_left (not_not_intro hc0)
      have hc2 := (affine_survives_one_of_two h02 hcd).resolve_left (not_not_intro hc0)
      rcases affine_survives_one_of_two h12 hab with ha1 | ha2
      · exact ⟨1, ha1, hc1⟩
      · exact ⟨2, ha2, hc2⟩
    · exact ⟨0, ha0, hc0⟩

/-- Every member of the pencil has some parity. This forces a *common* parity
on the union of the two endpoint supports, without a common-parity premise. -/
 theorem pencil_support_parity [Fintype ι] [CommRing K] [NoZeroDivisors K]
    (s : Fin 3 → K) (hs : Function.Injective s) (A B : Tensor K ι)
    (h : ∀ j, HasParity (fun x => A x - s j * B x))
    (x y : ι → Bool) (hx : A x ≠ 0 ∨ B x ≠ 0) (hy : A y ≠ 0 ∨ B y ≠ 0) :
    parity x = parity y := by
  obtain ⟨j, hjx, hjy⟩ := affine_two_coordinates_survive s hs hx hy
  exact h j x y hjx hjy

/-- Reinsert the bits at the two named, distinct port occurrences. -/
noncomputable def extendBits (a b : ι) (hab : a ≠ b)
    (y : Remaining a b → Bool) (u v : Bool) : ι → Bool :=
  fun i => Sum.elim y (fun t : Bool => if t then v else u) (splitPorts a b hab i)

 theorem extendBits_restrict (a b : ι) (hab : a ≠ b) (x : ι → Bool) :
    extendBits a b hab (restrict a b x) (x a) (x b) = x := by
  classical
  funext i
  by_cases ha : i = a
  · subst i
    simp [extendBits, splitPorts, Sum.elim]
  · by_cases hb : i = b
    · subst i
      simp [extendBits, splitPorts, Sum.elim, hab, Ne.symm hab]
    · simp [extendBits, splitPorts, Sum.elim, ha, hb, restrict]

 theorem parity_extend_equal [Fintype ι] (a b : ι) (hab : a ≠ b)
    (y : Remaining a b → Bool) (t : Bool) :
    parity (extendBits a b hab y t t) = parity y := by
  classical
  have hw := weight_reindex (splitPorts a b hab)
    (Sum.elim y (fun c : Bool => if c then t else t))
  change weight (extendBits a b hab y t t) = _ at hw
  rw [weight_sum] at hw
  unfold parity
  rw [hw]
  cases t <;> simp [weight, Fintype.sum_bool, Nat.add_mod]

 theorem parity_restrict_equal [Fintype ι] (a b : ι) (hab : a ≠ b)
    (x : ι → Bool) (heq : x a = x b) :
    parity (restrict a b x) = parity x := by
  have h := parity_extend_equal a b hab (restrict a b x) (x a)
  have hr := extendBits_restrict a b hab x
  rw [← heq] at hr
  rw [hr] at h
  exact h.symm

/-- The actual Walsh plus kernel diag(1,-s). -/
def plusKernel [Ring K] (s : K) : Kernel K :=
  fun u v => if u = v then if u then -s else 1 else 0

/-- Literal two-port bilinear contraction, retaining the zero table. -/
noncomputable def plusContraction [CommRing K] (a b : ι) (hab : a ≠ b)
    (s : K) (f : Tensor K ι) : Tensor K (Remaining a b) :=
  fun y => ∑ u : Bool, ∑ v : Bool,
    plusKernel s u v * f (extendBits a b hab y u v)

 theorem plusContraction_apply [CommRing K] (a b : ι) (hab : a ≠ b)
    (s : K) (f : Tensor K ι) (y : Remaining a b → Bool) :
    plusContraction a b hab s f y =
      f (extendBits a b hab y false false) - s * f (extendBits a b hab y true true) := by
  simp [plusContraction, plusKernel, Fintype.sum_bool, sub_eq_add_neg]
  ring

/-- A supported equal-bit word contributes a nontrivial affine coordinate. -/
 theorem endpoint_pair_nonzero [Zero K] (a b : ι) (hab : a ≠ b)
    (f : Tensor K ι) (x : ι → Bool) (hx : f x ≠ 0) (heq : x a = x b) :
    f (extendBits a b hab (restrict a b x) false false) ≠ 0 ∨
      f (extendBits a b hab (restrict a b x) true true) ≠ 0 := by
  have h := extendBits_restrict a b hab x
  rw [← heq] at h
  cases hbit : x a
  · left
    simp only [hbit] at h
    rwa [h]
  · right
    simp only [hbit] at h
    rwa [h]

/-- Three phase contractions of one port pair force the same parity on both
equal-bit endpoint slices together. -/
 theorem equal_slices_have_common_parity [Fintype ι] [CommRing K] [NoZeroDivisors K]
    (a b : ι) (hab : a ≠ b) (s : Fin 3 → K) (hs : Function.Injective s)
    (f : Tensor K ι) (h : ∀ j, HasParity (plusContraction a b hab (s j) f))
    (x y : Remaining a b → Bool)
    (hx : f (extendBits a b hab x false false) ≠ 0 ∨
      f (extendBits a b hab x true true) ≠ 0)
    (hy : f (extendBits a b hab y false false) ≠ 0 ∨
      f (extendBits a b hab y true true) ≠ 0) : parity x = parity y := by
  apply pencil_support_parity s hs
    (fun z => f (extendBits a b hab z false false))
    (fun z => f (extendBits a b hab z true true)) ?_ x y hx hy
  intro j
  simpa only [HasParity, plusContraction_apply] using h j

/-- The only collision-free arity-four situation lists all four Boolean pairs;
then both words have weight two. Larger port sets force a collision outright. -/
 theorem opposite_parities_repeat_pair [Fintype ι]
    (hcard : 4 ≤ Fintype.card ι) (x y : ι → Bool) (hpar : parity x ≠ parity y) :
    ∃ a b : ι, a ≠ b ∧ x a = x b ∧ y a = y b := by
  classical
  by_contra hnone
  let pair : ι → Bool × Bool := fun i => (x i, y i)
  have hinj : Function.Injective pair := by
    intro a b hp
    by_contra hab
    exact hnone ⟨a, b, hab, congrArg Prod.fst hp, congrArg Prod.snd hp⟩
  have hle := Fintype.card_le_of_injective pair hinj
  have heq : Fintype.card ι = Fintype.card (Bool × Bool) := by
    simp only [Fintype.card_prod, Fintype.card_bool] at hle ⊢
    omega
  let e : ι ≃ Bool × Bool := Equiv.ofBijective pair
    ((Fintype.bijective_iff_injective_and_card pair).mpr ⟨hinj, heq⟩)
  have hx : weight x = 2 := calc
    weight x = weight (fun p : Bool × Bool => p.1) := by
      simpa only [e, pair, Equiv.ofBijective_apply] using
        (weight_reindex e (fun p : Bool × Bool => p.1))
    _ = 2 := by decide
  have hy : weight y = 2 := calc
    weight y = weight (fun p : Bool × Bool => p.2) := by
      simpa only [e, pair, Equiv.ofBijective_apply] using
        (weight_reindex e (fun p : Bool × Bool => p.2))
    _ = 2 := by decide
  exact hpar (by simp [parity, hx, hy])

/-- The coefficient-table core of Lemma 5.10. The three contraction parities
are independently existential, and the zero tensor is a legal contraction.
The theorem includes arity four and every larger arity. -/
 theorem hasParity_of_three_phase_contractions [Fintype ι]
    [CommRing K] [NoZeroDivisors K]
    (hcard : 4 ≤ Fintype.card ι) (s : Fin 3 → K) (hs : Function.Injective s)
    (f : Tensor K ι)
    (h : ∀ (a b : ι) (hab : a ≠ b) (j : Fin 3),
      HasParity (plusContraction a b hab (s j) f)) : HasParity f := by
  intro x y hx hy
  by_contra hpar
  obtain ⟨a, b, hab, hxpair, hypair⟩ := opposite_parities_repeat_pair hcard x y hpar
  have hp := equal_slices_have_common_parity a b hab s hs f (h a b hab)
    (restrict a b x) (restrict a b y)
    (endpoint_pair_nonzero a b hab f x hx hxpair)
    (endpoint_pair_nonzero a b hab f y hy hypair)
  rw [parity_restrict_equal a b hab x hxpair,
    parity_restrict_equal a b hab y hypair] at hp
  exact hpar hp

/-- Equivalent input phrased only for nonzero contractions. No zero table is
removed from the contraction operation itself. -/
 theorem hasParity_of_nonzero_three_phase_contractions [Fintype ι]
    [CommRing K] [NoZeroDivisors K]
    (hcard : 4 ≤ Fintype.card ι) (s : Fin 3 → K) (hs : Function.Injective s)
    (f : Tensor K ι)
    (h : ∀ (a b : ι) (hab : a ≠ b) (j : Fin 3),
      plusContraction a b hab (s j) f ≠ 0 →
      HasParity (plusContraction a b hab (s j) f)) : HasParity f := by
  classical
  apply hasParity_of_three_phase_contractions hcard s hs f
  intro a b hab j
  by_cases hz : plusContraction a b hab (s j) f = 0
  · rw [hz]
    exact hasParity_zero
  · exact h a b hab j hz

 theorem exists_equal_bits [Fintype ι] (hcard : 3 ≤ Fintype.card ι)
    (x : ι → Bool) : ∃ a b : ι, a ≠ b ∧ x a = x b := by
  classical
  by_contra hnone
  have hinj : Function.Injective x := by
    intro a b h
    by_contra hab
    exact hnone ⟨a, b, hab, h⟩
  have hle := Fintype.card_le_of_injective x hinj
  simp only [Fintype.card_bool] at hle
  omega

/-- The cyclic case is stronger: two distinct phases of even contractions
already force the original tensor to be even. -/
 theorem even_of_even_contractions [Fintype ι] [CommRing K] [NoZeroDivisors K]
    (hcard : 3 ≤ Fintype.card ι) (s t : K) (hst : s ≠ t) (f : Tensor K ι)
    (h : ∀ (a b : ι) (hab : a ≠ b),
      SupportedOnParity (plusContraction a b hab s f) 0 ∧
      SupportedOnParity (plusContraction a b hab t f) 0) :
    SupportedOnParity f 0 := by
  intro x hx
  obtain ⟨a, b, hab, heq⟩ := exists_equal_bits hcard x
  have hend := endpoint_pair_nonzero a b hab f x hx heq
  have hp : parity (restrict a b x) = 0 := by
    rcases affine_survives_one_of_two hst hend with hs | ht
    · apply (h a b hab).1
      simpa only [plusContraction_apply] using hs
    · apply (h a b hab).2
      simpa only [plusContraction_apply] using ht
  rwa [parity_restrict_equal a b hab x heq] at hp

/-- Multiplication by a nonzero representative scalar preserves the exact
support, as required for the actual lambda_s K_s^+ contractions. -/
 theorem hasParity_scale_iff [Fintype ι] [CommRing K] [NoZeroDivisors K]
    (c : K) (hc : c ≠ 0) (f : Tensor K ι) :
    HasParity (fun x => c * f x) ↔ HasParity f := by
  constructor
  · intro h x y hx hy
    exact h x y (mul_ne_zero hc hx) (mul_ne_zero hc hy)
  · intro h x y hx hy
    exact h x y (mul_ne_zero_iff.mp hx).2 (mul_ne_zero_iff.mp hy).2

 theorem supportedOnParity_scale_iff [Fintype ι] [CommRing K] [NoZeroDivisors K]
    (c : K) (hc : c ≠ 0) (f : Tensor K ι) (p : ℕ) :
    SupportedOnParity (fun x => c * f x) p ↔ SupportedOnParity f p := by
  constructor
  · intro h x hx
    exact h x (mul_ne_zero hc hx)
  · intro h x hx
    exact h x (mul_ne_zero_iff.mp hx).2

/-- Main theorem with a separate arbitrary nonzero representative scalar for
every ordered pair and phase. -/
 theorem hasParity_of_scaled_three_phase_contractions [Fintype ι]
    [CommRing K] [NoZeroDivisors K]
    (hcard : 4 ≤ Fintype.card ι) (s : Fin 3 → K) (hs : Function.Injective s)
    (f : Tensor K ι) (c : ι → ι → Fin 3 → K)
    (hc : ∀ a b j, c a b j ≠ 0)
    (h : ∀ (a b : ι) (hab : a ≠ b) (j : Fin 3),
      HasParity (fun y => c a b j * plusContraction a b hab (s j) f y)) :
    HasParity f := by
  apply hasParity_of_three_phase_contractions hcard s hs f
  intro a b hab j
  exact (hasParity_scale_iff _ (hc a b j) _).mp (h a b hab j)

/-- Read a binary coefficient matrix as a tensor with two ordered Bool ports. -/
def kernelTensor (A : Kernel K) : Tensor K Bool := fun x => A (x false) (x true)

 theorem binary_diagonal_even [Zero K] (A : Kernel K)
    (h01 : A false true = 0) (h10 : A true false = 0) :
    SupportedOnParity (kernelTensor A) 0 := by
  intro x hx
  cases h0 : x false <;> cases h1 : x true
  · simp only [parity, weight, Fintype.sum_bool, h0, h1]; norm_num
  · exact False.elim (hx (by simp [kernelTensor, h0, h1, h01]))
  · exact False.elim (hx (by simp [kernelTensor, h0, h1, h10]))
  · simp only [parity, weight, Fintype.sum_bool, h0, h1]; norm_num

 theorem binary_antidiagonal_odd [Zero K] (A : Kernel K)
    (h00 : A false false = 0) (h11 : A true true = 0) :
    SupportedOnParity (kernelTensor A) 1 := by
  intro x hx
  cases h0 : x false <;> cases h1 : x true
  · exact False.elim (hx (by simp [kernelTensor, h0, h1, h00]))
  · simp only [parity, weight, Fintype.sum_bool, h0, h1]; norm_num
  · simp only [parity, weight, Fintype.sum_bool, h0, h1]; norm_num
  · exact False.elim (hx (by simp [kernelTensor, h0, h1, h11]))

/-- Genuine binary monomial matrices have one support parity. -/
 theorem binary_monomial_hasParity [Zero K] (A : Kernel K)
    (h : (A false true = 0 ∧ A true false = 0) ∨
      (A false false = 0 ∧ A true true = 0)) : HasParity (kernelTensor A) := by
  rcases h with h | h
  · exact supportedOnParity_hasParity (binary_diagonal_even A h.1 h.2)
  · exact supportedOnParity_hasParity (binary_antidiagonal_odd A h.1 h.2)

/-- Weight splits over the actual disjoint port blocks of a tensor product. -/
 theorem weight_decomposition [CommMonoid K] {n : ℕ}
    (D : TensorDecomposition K n) (x : Fin n → Bool) :
    weight x = ∑ i, weight (fun j => x (D.ports ⟨i, j⟩)) := by
  rw [← weight_reindex D.ports x]
  simp only [weight, Fintype.sum_sigma]

 theorem decomposition_factor_nonzero [CommRing K] {n : ℕ}
    (D : TensorDecomposition K n) (x : Fin n → Bool) (hx : D.value x ≠ 0)
    (i : Fin D.count) : D.factor i (fun j => x (D.ports ⟨i, j⟩)) ≠ 0 := by
  intro hi
  have hz : (∏ k, D.factor k (fun j => x (D.ports ⟨k, j⟩))) = 0 :=
    Finset.prod_eq_zero (Finset.mem_univ i) hi
  exact hx (by simp [TensorDecomposition.value, hz])

/-- Positive-arity factors having individually chosen parities implies parity
of their actual finite tensor product. Nullary factors are handled explicitly. -/
 theorem hasParity_decomposition [CommRing K] {n : ℕ}
    (D : TensorDecomposition K n)
    (h : ∀ i, 0 < D.arity i → HasParity (D.factor i)) : HasParity D.value := by
  intro x y hx hy
  have hp : ∀ i, parity (fun j => x (D.ports ⟨i, j⟩)) =
      parity (fun j => y (D.ports ⟨i, j⟩)) := by
    intro i
    by_cases hi : 0 < D.arity i
    · exact h i hi _ _ (decomposition_factor_nonzero D x hx i)
        (decomposition_factor_nonzero D y hy i)
    · have hxi := weight_le_card (fun j => x (D.ports ⟨i, j⟩))
      have hyi := weight_le_card (fun j => y (D.ports ⟨i, j⟩))
      simp only [Fintype.card_fin] at hxi hyi
      unfold parity
      omega
  unfold parity
  rw [weight_decomposition D x, weight_decomposition D y]
  conv_lhs => rw [Finset.sum_nat_mod]
  conv_rhs => rw [Finset.sum_nat_mod]
  congr 1
  exact Finset.sum_congr rfl (fun i _ => hp i)

/-- In the cyclic branch all positive factors are even, hence the product is
even. No parity assumption is needed for scalar (nullary) factors. -/
 theorem even_decomposition [CommRing K] {n : ℕ}
    (D : TensorDecomposition K n)
    (h : ∀ i, 0 < D.arity i → SupportedOnParity (D.factor i) 0) :
    SupportedOnParity D.value 0 := by
  intro x hx
  have hp : ∀ i, parity (fun j => x (D.ports ⟨i, j⟩)) = 0 := by
    intro i
    by_cases hi : 0 < D.arity i
    · exact h i hi _ (decomposition_factor_nonzero D x hx i)
    · have hxi := weight_le_card (fun j => x (D.ports ⟨i, j⟩))
      simp only [Fintype.card_fin] at hxi
      unfold parity
      omega
  unfold parity
  rw [weight_decomposition D x, Finset.sum_nat_mod]
  have hz : (∑ i, weight (fun j => x (D.ports ⟨i, j⟩)) % 2) = 0 :=
    Finset.sum_eq_zero (fun i _ => hp i)
  rw [hz]

 theorem hasParity_reindex [Fintype ι] [Fintype κ] [Zero K]
    (e : ι ≃ κ) (f : Tensor K ι) (h : HasParity f) :
    HasParity (Tensor.reindex e f) := by
  intro x y hx hy
  have hp := h (fun i => x (e i)) (fun i => y (e i)) hx hy
  simpa only [parity, weight_reindex] using hp

 theorem supportedOnParity_reindex [Fintype ι] [Fintype κ] [Zero K]
    (e : ι ≃ κ) (f : Tensor K ι) (p : ℕ) (h : SupportedOnParity f p) :
    SupportedOnParity (Tensor.reindex e f) p := by
  intro x hx
  have hp := h (fun i => x (e i)) hx
  simpa only [parity, weight_reindex] using hp

/-- Any finite phase set of size at least three supplies the three distinct
phases used by the coefficient argument. -/
 theorem hasParity_of_phase_set_contractions [Fintype ι]
    [CommRing K] [NoZeroDivisors K]
    (hcard : 4 ≤ Fintype.card ι) (S : Finset K) (hS : 3 ≤ S.card)
    (f : Tensor K ι)
    (h : ∀ (a b : ι) (hab : a ≠ b) (s : K), s ∈ S →
      HasParity (plusContraction a b hab s f)) : HasParity f := by
  classical
  obtain ⟨e⟩ : Nonempty (Fin 3 ↪ S) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hS)
  apply hasParity_of_three_phase_contractions hcard (fun j => (e j).val)
    (fun i j hij => e.injective (Subtype.ext hij)) f
  intro a b hab j
  exact h a b hab (e j).val (e j).property

/-- The verified finite-factor bridge combined with the actual-contraction
argument. This input records literal decompositions with port bijections; the
parities of different factors, phases and port pairs may all differ. -/
 theorem hasParity_of_contraction_factorizations [Fintype ι]
    [CommRing K] [NoZeroDivisors K]
    (hcard : 4 ≤ Fintype.card ι) (s : Fin 3 → K) (hs : Function.Injective s)
    (f : Tensor K ι)
    (h : ∀ (a b : ι) (hab : a ≠ b) (j : Fin 3),
      plusContraction a b hab (s j) f ≠ 0 →
      ∃ (n : ℕ) (D : TensorDecomposition K n) (e : Fin n ≃ Remaining a b),
        (∀ i, 0 < D.arity i → HasParity (D.factor i)) ∧
        Tensor.reindex e D.value = plusContraction a b hab (s j) f) : HasParity f := by
  apply hasParity_of_nonzero_three_phase_contractions hcard s hs f
  intro a b hab j hn
  obtain ⟨n, D, e, hp, he⟩ := h a b hab j hn
  rw [← he]
  exact hasParity_reindex e D.value (hasParity_decomposition D hp)

/-- Cyclic counterpart with literal factor decompositions for each of two
phases. Positive-arity factors must be even; nullary scalars remain arbitrary. -/
 theorem even_of_contraction_factorizations [Fintype ι]
    [CommRing K] [NoZeroDivisors K]
    (hcard : 3 ≤ Fintype.card ι) (s t : K) (hst : s ≠ t) (f : Tensor K ι)
    (h : ∀ (a b : ι) (hab : a ≠ b) (q : K), q = s ∨ q = t →
      plusContraction a b hab q f ≠ 0 →
      ∃ (n : ℕ) (D : TensorDecomposition K n) (e : Fin n ≃ Remaining a b),
        (∀ i, 0 < D.arity i → SupportedOnParity (D.factor i) 0) ∧
        Tensor.reindex e D.value = plusContraction a b hab q f) :
    SupportedOnParity f 0 := by
  classical
  apply even_of_even_contractions hcard s t hst f
  intro a b hab
  have hp : ∀ q, q = s ∨ q = t → SupportedOnParity (plusContraction a b hab q f) 0 := by
    intro q hq
    by_cases hz : plusContraction a b hab q f = 0
    · intro x hx
      exact False.elim (hx (congrFun hz x))
    · obtain ⟨n, D, e, hD, he⟩ := h a b hab q hq hz
      rw [← he]
      exact supportedOnParity_reindex e D.value 0 (even_decomposition D hD)
  exact ⟨hp s (Or.inl rfl), hp t (Or.inr rfl)⟩

/-- Root-of-unity specialization, with the phase cardinality proved from a
primitive root instead of being added as a contraction hypothesis. -/
 theorem hasParity_of_root_of_unity_contractions [Fintype ι] [Field K]
    (hcard : 4 ≤ Fintype.card ι) (N : ℕ) (hN : 3 ≤ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ N) (f : Tensor K ι)
    (h : ∀ (a b : ι) (hab : a ≠ b) (s : K), s ^ N = 1 →
      HasParity (plusContraction a b hab s f)) : HasParity f := by
  apply hasParity_of_phase_set_contractions hcard (Polynomial.nthRootsFinset N (1 : K))
    (by rw [hζ.card_nthRootsFinset]; exact hN) f
  intro a b hab s hs
  exact h a b hab s ((Polynomial.mem_nthRootsFinset (by omega : 0 < N) 1).mp hs)

/-- Over the complex numbers the required primitive root exists for every
N >= 3. Oddness is not needed by the support-parity argument itself. -/
 theorem complex_hasParity_of_root_of_unity_contractions [Fintype ι]
    (hcard : 4 ≤ Fintype.card ι) (N : ℕ) (hN : 3 ≤ N) (f : Tensor ℂ ι)
    (h : ∀ (a b : ι) (hab : a ≠ b) (s : ℂ), s ^ N = 1 →
      HasParity (plusContraction a b hab s f)) : HasParity f := by
  exact hasParity_of_root_of_unity_contractions hcard N hN _
    (Complex.isPrimitiveRoot_exp N (by omega)) f h

 theorem even_of_root_of_unity_contractions [Fintype ι] [Field K]
    (hcard : 3 ≤ Fintype.card ι) (N : ℕ) (hN : 2 ≤ N)
    (ζ : K) (hζ : IsPrimitiveRoot ζ N) (f : Tensor K ι)
    (h : ∀ (a b : ι) (hab : a ≠ b) (s : K), s ^ N = 1 →
      SupportedOnParity (plusContraction a b hab s f) 0) :
    SupportedOnParity f 0 := by
  apply even_of_even_contractions hcard 1 ζ (Ne.symm (hζ.ne_one (by omega))) f
  intro a b hab
  exact ⟨h a b hab 1 (one_pow N), h a b hab ζ hζ.pow_eq_one⟩

 theorem complex_even_of_root_of_unity_contractions [Fintype ι]
    (hcard : 3 ≤ Fintype.card ι) (N : ℕ) (hN : 2 ≤ N) (f : Tensor ℂ ι)
    (h : ∀ (a b : ι) (hab : a ≠ b) (s : ℂ), s ^ N = 1 →
      SupportedOnParity (plusContraction a b hab s f) 0) :
    SupportedOnParity f 0 := by
  exact even_of_root_of_unity_contractions hcard N hN _
    (Complex.isPrimitiveRoot_exp N (by omega)) f h

/-- The arity-two cyclic transfer calculation is the literal matrix product
D Z, for any diagonal D. No parity conclusion is used as an assumption. -/
 theorem binary_diagonal_transfer_times_Z_even [CommRing K] (D : Kernel K)
    (h01 : D false true = 0) (h10 : D true false = 0) :
    SupportedOnParity (kernelTensor (Kernel.mul D Bell.Z)) 0 := by
  apply binary_diagonal_even
  · simp [Kernel.mul_apply, Bell.Z, Bell.ordered, Bell.sign, h01]
  · simp [Kernel.mul_apply, Bell.Z, Bell.ordered, Bell.sign, h10]

/-- The arity-two reflection transfer calculation is the literal product A Z
for any antidiagonal A. -/
 theorem binary_antidiagonal_transfer_times_Z_odd [CommRing K] (A : Kernel K)
    (h00 : A false false = 0) (h11 : A true true = 0) :
    SupportedOnParity (kernelTensor (Kernel.mul A Bell.Z)) 1 := by
  apply binary_antidiagonal_odd
  · simp [Kernel.mul_apply, Bell.Z, Bell.ordered, Bell.sign, h00]
  · simp [Kernel.mul_apply, Bell.Z, Bell.ordered, Bell.sign, h11]

end Paper2.HeightOne
