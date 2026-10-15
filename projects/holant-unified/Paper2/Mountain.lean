import Paper2.Charge
import Mathlib.Logic.Equiv.Fintype

/-!
# Mountains (paper 2, Definition 2.3 and Section 4)

These theorems concern actual coefficient tables and their support. In
particular, divisibility plus the arity bound really implies the three-layer
restriction used in the charge-bridge proof; it is not assumed as an oracle.
-/

namespace Paper2

variable {K : Type*} {d : ℕ}

/-- A height-`d` mountain has two nonzero extreme coefficients and may have
arbitrary coefficients in the central layer. -/
structure IsMountain [Zero K] (M : Signature K (2 * d)) : Prop where
  height_pos : 0 < d
  support_layers : ∀ x, M x ≠ 0 →
    x = (fun _ => false) ∨ halfCharge x = 0 ∨ x = (fun _ => true)
  zero_ne_zero : M (fun _ => false) ≠ 0
  one_ne_zero : M (fun _ => true) ≠ 0

/-- The set of integer half-charges that actually occur in the support. -/
def supportedHalfCharges [Zero K] {ι : Type*} [Fintype ι]
    (f : Tensor K ι) : Set ℤ := {c | ∃ x, f x ≠ 0 ∧ halfCharge x = c}

theorem isMountain_iff_supportedHalfCharges [Zero K]
    (M : Signature K (2 * d)) :
    IsMountain M ↔ 0 < d ∧
      (∀ c ∈ supportedHalfCharges M, c = -(d : ℤ) ∨ c = 0 ∨ c = (d : ℤ)) ∧
      -(d : ℤ) ∈ supportedHalfCharges M ∧ (d : ℤ) ∈ supportedHalfCharges M := by
  constructor
  · intro h
    refine ⟨h.height_pos, ?_, ?_, ?_⟩
    · rintro c ⟨x, hx, rfl⟩
      rcases h.support_layers x hx with hz | hc | ho
      · subst x
        exact Or.inl (halfCharge_false d)
      · exact Or.inr (Or.inl hc)
      · subst x
        exact Or.inr (Or.inr (halfCharge_true d))
    · exact ⟨_, h.zero_ne_zero, halfCharge_false d⟩
    · exact ⟨_, h.one_ne_zero, halfCharge_true d⟩
  · rintro ⟨hd, hs, hz, ho⟩
    refine ⟨hd, ?_, ?_, ?_⟩
    · intro x hx
      rcases hs _ ⟨x, hx, rfl⟩ with h | h | h
      · exact Or.inl ((halfCharge_eq_neg_height_iff x).mp h)
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ((halfCharge_eq_height_iff x).mp h))
    · obtain ⟨x, hx, hc⟩ := hz
      simpa only [(halfCharge_eq_neg_height_iff x).mp hc] using hx
    · obtain ⟨x, hx, hc⟩ := ho
      simpa only [(halfCharge_eq_height_iff x).mp hc] using hx

/-- The endpoint product convention in the manuscript is equivalent over a
domain to the two separate nonvanishing statements in `IsMountain`. -/
theorem isMountain_iff_endpoint_product [Semiring K] [NoZeroDivisors K]
    (M : Signature K (2 * d)) :
    IsMountain M ↔ 0 < d ∧
      (∀ x, M x ≠ 0 → weight x = 0 ∨ weight x = d ∨ weight x = 2 * d) ∧
      M (fun _ => false) * M (fun _ => true) ≠ 0 := by
  constructor
  · intro h
    refine ⟨h.height_pos, ?_, mul_ne_zero h.zero_ne_zero h.one_ne_zero⟩
    intro x hx
    rcases h.support_layers x hx with hz | hc | ho
    · exact Or.inl ((weight_eq_zero_iff x).mpr hz)
    · exact Or.inr (Or.inl ((halfCharge_eq_zero_iff x).mp hc))
    · exact Or.inr (Or.inr (by simpa using (weight_eq_card_iff x).mpr ho))
  · rintro ⟨hd, hs, he⟩
    refine ⟨hd, ?_, left_ne_zero_of_mul he, right_ne_zero_of_mul he⟩
    intro x hx
    rcases hs x hx with hz | hc | ho
    · exact Or.inl ((weight_eq_zero_iff x).mp hz)
    · exact Or.inr (Or.inl ((halfCharge_eq_zero_iff x).mpr hc))
    · exact Or.inr (Or.inr ((weight_eq_card_iff x).mp (by simpa using ho)))

/-- The elementary interval step used after reducing arity to twice the gcd. -/
theorem eq_neg_or_zero_or_pos_of_dvd_of_bounds {a c : ℤ} (ha : 0 < a)
    (hc : a ∣ c) (hl : -a ≤ c) (hu : c ≤ a) :
    c = -a ∨ c = 0 ∨ c = a := by
  obtain ⟨k, rfl⟩ := hc
  have hk₁ : -1 ≤ k := by nlinarith
  have hk₂ : k ≤ 1 := by nlinarith
  have hk : k = -1 ∨ k = 0 ∨ k = 1 := by omega
  rcases hk with rfl | rfl | rfl <;> simp

/-- All possible supported charges at arity `2*d` are the three claimed values. -/
theorem halfCharge_three_values_of_dvd (hd : 0 < d)
    (x : Fin (2 * d) → Bool) (hx : (d : ℤ) ∣ halfCharge x) :
    halfCharge x = -(d : ℤ) ∨ halfCharge x = 0 ∨ halfCharge x = (d : ℤ) := by
  have hb := halfCharge_bounds x
  exact eq_neg_or_zero_or_pos_of_dvd_of_bounds (by exact_mod_cast hd) hx hb.1 hb.2

/-- Section 4's divisibility-to-mountain step, with both endpoint witnesses
explicit and no gadget-accessibility assumption built into the conclusion. -/
theorem isMountain_of_halfChargeDivisible [Zero K]
    {M : Signature K (2 * d)} (hd : 0 < d)
    (hdiv : Tensor.HalfChargeDivisible M d)
    (hz : M (fun _ => false) ≠ 0) (ho : M (fun _ => true) ≠ 0) :
    IsMountain M := by
  refine ⟨hd, ?_, hz, ho⟩
  intro x hx
  rcases halfCharge_three_values_of_dvd hd x (hdiv x hx) with h | h | h
  · exact Or.inl ((halfCharge_eq_neg_height_iff x).mp h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ((halfCharge_eq_height_iff x).mp h))

/-- A mountain genuinely contains both charge signs. -/
theorem IsMountain.two_sided [Zero K] {M : Signature K (2 * d)}
    (h : IsMountain M) :
    (∃ x, M x ≠ 0 ∧ halfCharge x < 0) ∧
    (∃ x, M x ≠ 0 ∧ 0 < halfCharge x) := by
  constructor
  · refine ⟨_, h.zero_ne_zero, ?_⟩
    rw [halfCharge_false]
    have := h.height_pos
    omega
  · refine ⟨_, h.one_ne_zero, ?_⟩
    rw [halfCharge_true]
    exact_mod_cast h.height_pos

/-- No positive-height mountain can live on one doubled-charge layer. -/
theorem IsMountain.not_chargeLayer [Zero K] {M : Signature K (2 * d)}
    (h : IsMountain M) (c : ℤ) : ¬ Tensor.ChargeLayer M c := by
  intro hc
  have hz := hc _ h.zero_ne_zero
  have ho := hc _ h.one_ne_zero
  simp only [doubledCharge, weight_false, weight_true, Fintype.card_fin] at hz ho
  have := h.height_pos
  omega

/-- At height one, every other word is central, so only the endpoints matter. -/
theorem isMountain_height_one_iff [Zero K] (M : Signature K (2 * 1)) :
    IsMountain M ↔ M (fun _ => false) ≠ 0 ∧ M (fun _ => true) ≠ 0 := by
  constructor
  · intro h
    exact ⟨h.zero_ne_zero, h.one_ne_zero⟩
  · rintro ⟨hz, ho⟩
    apply isMountain_of_halfChargeDivisible (by omega) _ hz ho
    intro x _
    exact one_dvd _

/-- This formalizes the obstruction stressed at the end of Section 4:
fixed native-X gadgets made of single-layer signatures cannot be mountains. -/
theorem Network.denote_not_isMountain [CommSemiring K]
    (N : Network K (2 * d)) (hX : ∀ e, N.edge e = Signature.disequality)
    (c : Fin N.shape.vertices → ℤ)
    (hc : ∀ v, Tensor.ChargeLayer (N.vertex v) (c v)) :
    ¬ IsMountain N.denote := by
  intro hm
  exact hm.not_chargeLayer _ (N.denote_chargeLayer hX c hc)

/-- The supported-charge arithmetic used after an actual native-X gadget
has been reduced to arity `2*d`. -/
theorem Network.denote_isMountain_of_endpoints [CommSemiring K]
    (N : Network K (2 * d)) (hd : 0 < d)
    (hlocal : ∀ v, Even (N.shape.arity v))
    (hX : ∀ e, N.edge e = Signature.disequality)
    (hdiv : ∀ v, Tensor.HalfChargeDivisible (N.vertex v) d)
    (hz : N.denote (fun _ => false) ≠ 0)
    (ho : N.denote (fun _ => true) ≠ 0) : IsMountain N.denote := by
  apply isMountain_of_halfChargeDivisible hd _ hz ho
  exact N.denote_halfChargeDivisible (even_two_mul d) hlocal hX d hdiv

/-- Hamming weight completely classifies Boolean words up to a port permutation. -/
theorem exists_portPermutation_of_weight_eq {ι : Type*} [Fintype ι]
    (x y : ι → Bool) (h : weight x = weight y) :
    ∃ e : Equiv.Perm ι, (fun i => y (e i)) = x := by
  classical
  have hc : Fintype.card {i // x i = true} = Fintype.card {i // y i = true} := by
    simpa [Fintype.card_subtype, weight] using h
  let e : {i // x i = true} ≃ {i // y i = true} := Fintype.equivOfCardEq hc
  refine ⟨e.extendSubtype, ?_⟩
  funext i
  cases hi : x i
  · have he := e.extendSubtype_not_mem i (by simp [hi])
    cases hy : y (e.extendSubtype i) <;> simp_all
  · exact e.extendSubtype_mem i hi

/-- A supported word can be moved to any prescribed word in the same layer. -/
theorem exists_reindex_evaluation [Zero K] {ι : Type*} [Fintype ι]
    (f : Tensor K ι) (x y : ι → Bool) (h : weight x = weight y) :
    ∃ e : Equiv.Perm ι, Tensor.reindex e f y = f x := by
  obtain ⟨e, he⟩ := exists_portPermutation_of_weight_eq x y h
  exact ⟨e, congrArg f he⟩

namespace MountainConstruction

open scoped BigOperators

/-- Two equal blocks, with possible support only at weights `0`, `d`, `2*d`. -/
def ThreeLayers [Zero K] (f : Tensor K (Fin d ⊕ Fin d)) : Prop :=
  ∀ x, f x ≠ 0 → weight x = 0 ∨ weight x = d ∨ weight x = 2 * d

/-- A missing zero endpoint forces the zero-external row's unique possible
internal extension to be the all-one word. -/
theorem zero_row_unique [Zero K] {f : Tensor K (Fin d ⊕ Fin d)}
    (_hd : 0 < d) (hf : ThreeLayers f) (hz : f (fun _ => false) = 0)
    (z : Fin d → Bool) (h : f (Sum.elim (fun _ => false) z) ≠ 0) :
    z = fun _ => true := by
  have hw := hf _ h
  have hb := weight_le_card z
  simp only [weight_sum, weight_false, zero_add, Fintype.card_fin] at hw hb
  have hn : weight z ≠ 0 := by
    intro he
    have he' := (weight_eq_zero_iff z).mp he
    subst z
    apply h
    convert hz using 1
    congr 1
    funext i
    cases i <;> rfl
  apply (weight_eq_card_iff z).mp
  simp only [Fintype.card_fin]
  omega

/-- The symmetric unique-extension statement at the one-external row. -/
theorem one_row_unique [Zero K] {f : Tensor K (Fin d ⊕ Fin d)}
    (_hd : 0 < d) (hf : ThreeLayers f) (ho : f (fun _ => true) = 0)
    (z : Fin d → Bool) (h : f (Sum.elim (fun _ => true) z) ≠ 0) :
    z = fun _ => false := by
  have hw := hf _ h
  have hb := weight_le_card z
  simp only [weight_sum, weight_true, Fintype.card_fin] at hw hb
  have hn : weight z ≠ d := by
    intro he
    have he' := (weight_eq_card_iff z).mp (by simpa using he)
    subst z
    apply h
    convert ho using 1
    congr 1
    funext i
    cases i <;> rfl
  apply (weight_eq_zero_iff z).mp
  omega

/-- The actual finite sum for joining the last `d` ports of two `2*d`-port
signatures with coordinatewise X edges, exposing their first `d` ports. -/
def joinX [CommSemiring K] (P N : Tensor K (Fin d ⊕ Fin d)) :
    Tensor K (Fin d ⊕ Fin d) :=
  fun x => ∑ z : Fin d → Bool,
    P (Sum.elim (fun i => x (.inl i)) z) *
      N (Sum.elim (fun i => x (.inr i)) (fun i => !(z i)))

/-- The first endpoint formula displayed in Section 4. -/
theorem joinX_zero_endpoint [CommSemiring K]
    {P N : Tensor K (Fin d ⊕ Fin d)}
    (hd : 0 < d) (hP : ThreeLayers P) (hPzero : P (fun _ => false) = 0) :
    joinX P N (fun _ => false) =
      P (Sum.elim (fun _ => false) (fun _ => true)) * N (fun _ => false) := by
  classical
  unfold joinX
  have he : Sum.elim (fun _ : Fin d => false) (fun _ : Fin d => false) =
      (fun _ : Fin d ⊕ Fin d => false) := by
    funext i
    cases i <;> rfl
  simpa only [Bool.not_true, he] using
    (Finset.sum_eq_single (fun _ : Fin d => true)
      (fun z _ hne => by
        have hz : P (Sum.elim (fun _ => false) z) = 0 := by
          by_contra hn
          exact hne (zero_row_unique hd hP hPzero z hn)
        simp only [hz, zero_mul]) (by simp) :
      (∑ z : Fin d → Bool, P (Sum.elim (fun _ => false) z) *
        N (Sum.elim (fun _ => false) (fun i => !(z i)))) = _)

/-- The second endpoint formula displayed in Section 4. -/
theorem joinX_one_endpoint [CommSemiring K]
    {P N : Tensor K (Fin d ⊕ Fin d)}
    (hd : 0 < d) (hN : ThreeLayers N) (hNone : N (fun _ => true) = 0) :
    joinX P N (fun _ => true) =
      P (fun _ => true) * N (Sum.elim (fun _ => true) (fun _ => false)) := by
  classical
  unfold joinX
  have he : Sum.elim (fun _ : Fin d => true) (fun _ : Fin d => true) =
      (fun _ : Fin d ⊕ Fin d => true) := by
    funext i
    cases i <;> rfl
  simpa only [Bool.not_true, he] using
    (Finset.sum_eq_single (fun _ : Fin d => true)
      (fun z _ hne => by
        have hz : N (Sum.elim (fun _ => true) (fun i => !(z i))) = 0 := by
          by_contra hn
          have hc := one_row_unique hd hN hNone (fun i => !(z i)) hn
          apply hne
          funext i
          have hi := congrFun hc i
          cases hzi : z i <;> simp_all
        simp only [hz, mul_zero]) (by simp) :
      (∑ z : Fin d → Bool, P (Sum.elim (fun _ => true) z) *
        N (Sum.elim (fun _ => true) (fun i => !(z i)))) = _)

/-- Local half-charge conservation for the explicit two-signature connector. -/
theorem joinX_halfCharge_identity (a b z : Fin d → Bool) :
    halfCharge (Sum.elim a z) + halfCharge (Sum.elim b (fun i => !(z i))) =
      halfCharge (Sum.elim a b) := by
  have hz := weight_complement_add z
  simp only [Fintype.card_fin] at hz
  simp only [halfCharge, weight_sum, Fintype.card_sum, Fintype.card_fin]
  omega

/-- The connector cannot create a half-charge outside the input divisibility lattice. -/
theorem joinX_halfChargeDivisible [CommSemiring K]
    {P N : Tensor K (Fin d ⊕ Fin d)} {a : ℤ}
    (hP : Tensor.HalfChargeDivisible P a) (hN : Tensor.HalfChargeDivisible N a) :
    Tensor.HalfChargeDivisible (joinX P N) a := by
  intro x hx
  classical
  by_contra hbad
  apply hx
  apply Finset.sum_eq_zero
  intro z _
  by_contra hz
  have hp := hP _ (left_ne_zero_of_mul hz)
  have hn := hN _ (right_ne_zero_of_mul hz)
  have hc := joinX_halfCharge_identity (fun i => x (.inl i)) (fun i => x (.inr i)) z
  have he : Sum.elim (fun i => x (.inl i)) (fun i => x (.inr i)) = x := by
    funext i
    cases i <;> rfl
  rw [he] at hc
  exact hbad (hc ▸ dvd_add hp hn)

/-- Reinterpret the two ordered blocks as a usual `2*d`-port signature. -/
noncomputable def blockEquiv (d : ℕ) : (Fin d ⊕ Fin d) ≃ Fin (2 * d) :=
  Fintype.equivOfCardEq (by simp; omega)

/-- The two-central-parts branch of Section 4, as a proved construction of an
actual mountain table. Accessibility of the input tables remains a separate
network/reduction question. -/
theorem joinX_isMountain [CommSemiring K] [NoZeroDivisors K]
    {P N : Tensor K (Fin d ⊕ Fin d)}
    (hd : 0 < d) (hP : ThreeLayers P) (hN : ThreeLayers N)
    (hPzero : P (fun _ => false) = 0) (hNone : N (fun _ => true) = 0)
    (hPone : P (fun _ => true) ≠ 0) (hNzero : N (fun _ => false) ≠ 0)
    (hPc : P (Sum.elim (fun _ => false) (fun _ => true)) ≠ 0)
    (hNc : N (Sum.elim (fun _ => true) (fun _ => false)) ≠ 0)
    (hPd : Tensor.HalfChargeDivisible P d) (hNd : Tensor.HalfChargeDivisible N d) :
    IsMountain (Tensor.reindex (blockEquiv d) (joinX P N)) := by
  apply isMountain_of_halfChargeDivisible hd
  · exact Tensor.reindex_halfChargeDivisible _ (joinX_halfChargeDivisible hPd hNd)
  · change joinX P N (fun _ => false) ≠ 0
    rw [joinX_zero_endpoint hd hP hPzero]
    exact mul_ne_zero hPc hNzero
  · change joinX P N (fun _ => true) ≠ 0
    rw [joinX_one_endpoint hd hN hNone]
    exact mul_ne_zero hPone hNc

/-- A scalar multiple of the all-zero point mass on the two internal blocks. -/
def zeroPointMass [Zero K] (n : K) : Tensor K (Fin d ⊕ Fin d) :=
  fun x => if x = (fun _ => false) then n else 0

/-- The three-signature connector from the one-central-part branch:
`N` joins by X edges to the last block of each of two copies of `P`. -/
def joinTwoCopiesX [CommSemiring K] (P N : Tensor K (Fin d ⊕ Fin d)) :
    Tensor K (Fin d ⊕ Fin d) :=
  fun x => ∑ z : Fin d → Bool, ∑ w : Fin d → Bool,
    (P (Sum.elim (fun i => x (.inl i)) z) *
      P (Sum.elim (fun i => x (.inr i)) w)) *
        N (Sum.elim (fun i => !(z i)) (fun i => !(w i)))

theorem complement_blocks_eq_zero (z w : Fin d → Bool) :
    Sum.elim (fun i => !(z i)) (fun i => !(w i)) = (fun _ => false) ↔
      z = (fun _ => true) ∧ w = (fun _ => true) := by
  constructor
  · intro h
    constructor
    · funext i
      have hi := congrFun h (.inl i)
      cases hz : z i <;> simp_all
    · funext i
      have hi := congrFun h (.inr i)
      cases hw : w i <;> simp_all
  · rintro ⟨rfl, rfl⟩
    funext i
    cases i <;> rfl

/-- Full evaluation of the one-central connector: the internal extension is
unique for every boundary word, not just at the two endpoints. -/
theorem joinTwoCopiesX_zeroPointMass [CommSemiring K]
    (P : Tensor K (Fin d ⊕ Fin d)) (n : K) (x : Fin d ⊕ Fin d → Bool) :
    joinTwoCopiesX P (zeroPointMass n) x =
      n * P (Sum.elim (fun i => x (.inl i)) (fun _ => true)) *
        P (Sum.elim (fun i => x (.inr i)) (fun _ => true)) := by
  classical
  simp [joinTwoCopiesX, zeroPointMass, complement_blocks_eq_zero, ite_and,
    mul_ite, mul_comm, mul_assoc]

/-- Half-charge accounting for the three-signature connector. -/
theorem joinTwoCopiesX_halfCharge_identity (a b z w : Fin d → Bool) :
    halfCharge (Sum.elim a z) + halfCharge (Sum.elim b w) +
      halfCharge (Sum.elim (fun i => !(z i)) (fun i => !(w i))) =
        halfCharge (Sum.elim a b) := by
  have hz := weight_complement_add z
  have hw := weight_complement_add w
  simp only [Fintype.card_fin] at hz hw
  simp only [halfCharge, weight_sum, Fintype.card_sum, Fintype.card_fin]
  omega

theorem joinTwoCopiesX_halfChargeDivisible [CommSemiring K]
    {P N : Tensor K (Fin d ⊕ Fin d)} {a : ℤ}
    (hP : Tensor.HalfChargeDivisible P a) (hN : Tensor.HalfChargeDivisible N a) :
    Tensor.HalfChargeDivisible (joinTwoCopiesX P N) a := by
  intro x hx
  classical
  by_contra hbad
  apply hx
  apply Finset.sum_eq_zero
  intro z _
  apply Finset.sum_eq_zero
  intro w _
  by_contra hz
  have hpz := hP _ (left_ne_zero_of_mul (left_ne_zero_of_mul hz))
  have hpw := hP _ (right_ne_zero_of_mul (left_ne_zero_of_mul hz))
  have hn := hN _ (right_ne_zero_of_mul hz)
  have hc := joinTwoCopiesX_halfCharge_identity
    (fun i => x (.inl i)) (fun i => x (.inr i)) z w
  have he : Sum.elim (fun i => x (.inl i)) (fun i => x (.inr i)) = x := by
    funext i
    cases i <;> rfl
  rw [he] at hc
  exact hbad (hc ▸ dvd_add (dvd_add hpz hpw) hn)

theorem zeroPointMass_halfChargeDivisible [Zero K] (n : K) :
    Tensor.HalfChargeDivisible (zeroPointMass (d := d) n) d := by
  intro x hx
  have he : x = (fun _ => false) := by
    by_contra h
    exact hx (by simp [zeroPointMass, h])
  subst x
  simp [halfCharge, Fintype.card_sum, ← two_mul]

/-- The one-central-part branch of Section 4 is also a genuine table-level
mountain construction, using exactly the displayed three-signature sum. -/
theorem joinTwoCopiesX_isMountain [CommSemiring K] [NoZeroDivisors K]
    (P : Tensor K (Fin d ⊕ Fin d)) (n : K)
    (hd : 0 < d) (hn : n ≠ 0)
    (hPone : P (fun _ => true) ≠ 0)
    (hPc : P (Sum.elim (fun _ => false) (fun _ => true)) ≠ 0)
    (hPd : Tensor.HalfChargeDivisible P d) :
    IsMountain (Tensor.reindex (blockEquiv d) (joinTwoCopiesX P (zeroPointMass n))) := by
  apply isMountain_of_halfChargeDivisible hd
  · exact Tensor.reindex_halfChargeDivisible _
      (joinTwoCopiesX_halfChargeDivisible hPd (zeroPointMass_halfChargeDivisible n))
  · change joinTwoCopiesX P (zeroPointMass n) (fun _ => false) ≠ 0
    rw [joinTwoCopiesX_zeroPointMass]
    exact mul_ne_zero (mul_ne_zero hn hPc) hPc
  · change joinTwoCopiesX P (zeroPointMass n) (fun _ => true) ≠ 0
    rw [joinTwoCopiesX_zeroPointMass]
    have he : Sum.elim (fun _ : Fin d => true) (fun _ : Fin d => true) =
        (fun _ : Fin d ⊕ Fin d => true) := by
      funext i
      cases i <;> rfl
    rw [he]
    exact mul_ne_zero (mul_ne_zero hn hPone) hPone

/-- A scalar multiple of the all-one point mass. -/
def onePointMass [Zero K] (n : K) : Tensor K (Fin d ⊕ Fin d) :=
  fun x => if x = (fun _ => true) then n else 0

theorem complement_blocks_eq_one (z w : Fin d → Bool) :
    Sum.elim (fun i => !(z i)) (fun i => !(w i)) = (fun _ => true) ↔
      z = (fun _ => false) ∧ w = (fun _ => false) := by
  constructor
  · intro h
    constructor
    · funext i
      have hi := congrFun h (.inl i)
      cases hz : z i <;> simp_all
    · funext i
      have hi := congrFun h (.inr i)
      cases hw : w i <;> simp_all
  · rintro ⟨rfl, rfl⟩
    funext i
    cases i <;> rfl

theorem joinTwoCopiesX_onePointMass [CommSemiring K]
    (N : Tensor K (Fin d ⊕ Fin d)) (p : K) (x : Fin d ⊕ Fin d → Bool) :
    joinTwoCopiesX N (onePointMass p) x =
      p * N (Sum.elim (fun i => x (.inl i)) (fun _ => false)) *
        N (Sum.elim (fun i => x (.inr i)) (fun _ => false)) := by
  classical
  simp [joinTwoCopiesX, onePointMass, complement_blocks_eq_one, ite_and,
    mul_ite, mul_comm, mul_assoc]

theorem onePointMass_halfChargeDivisible [Zero K] (p : K) :
    Tensor.HalfChargeDivisible (onePointMass (d := d) p) d := by
  intro x hx
  have he : x = (fun _ => true) := by
    by_contra h
    exact hx (by simp [onePointMass, h])
  subst x
  simp [halfCharge, Fintype.card_sum, ← two_mul]

/-- The mirror one-central-part case is proved by its actual coefficient sum. -/
theorem joinTwoCopiesX_mirror_isMountain [CommSemiring K] [NoZeroDivisors K]
    (N : Tensor K (Fin d ⊕ Fin d)) (p : K)
    (hd : 0 < d) (hp : p ≠ 0)
    (hNzero : N (fun _ => false) ≠ 0)
    (hNc : N (Sum.elim (fun _ => true) (fun _ => false)) ≠ 0)
    (hNd : Tensor.HalfChargeDivisible N d) :
    IsMountain (Tensor.reindex (blockEquiv d) (joinTwoCopiesX N (onePointMass p))) := by
  apply isMountain_of_halfChargeDivisible hd
  · exact Tensor.reindex_halfChargeDivisible _
      (joinTwoCopiesX_halfChargeDivisible hNd (onePointMass_halfChargeDivisible p))
  · change joinTwoCopiesX N (onePointMass p) (fun _ => false) ≠ 0
    rw [joinTwoCopiesX_onePointMass]
    have he : Sum.elim (fun _ : Fin d => false) (fun _ : Fin d => false) =
        (fun _ : Fin d ⊕ Fin d => false) := by
      funext i
      cases i <;> rfl
    rw [he]
    exact mul_ne_zero (mul_ne_zero hp hNzero) hNzero
  · change joinTwoCopiesX N (onePointMass p) (fun _ => true) ≠ 0
    rw [joinTwoCopiesX_onePointMass]
    exact mul_ne_zero (mul_ne_zero hp hNc) hNc

/-- If a three-layer table has neither a central part nor a one endpoint,
its remaining scalar times the zero point mass is the entire table. -/
theorem eq_zeroPointMass_of_no_center [Zero K]
    {N : Tensor K (Fin d ⊕ Fin d)} (hN : ThreeLayers N)
    (hNone : N (fun _ => true) = 0)
    (hc : ∀ x, weight x = d → N x = 0) :
    N = zeroPointMass (N (fun _ => false)) := by
  classical
  funext x
  by_cases hx : x = (fun _ => false)
  · simp [zeroPointMass, hx]
  · simp only [zeroPointMass, ite_eq_right hx]
    by_contra hn
    rcases hN x hn with h | h | h
    · exact hx ((weight_eq_zero_iff x).mp h)
    · exact hn (hc x h)
    · have he := (weight_eq_card_iff x).mp (by simpa [Fintype.card_sum, two_mul] using h)
      exact hn (he ▸ hNone)

/-- The symmetric pure-one normal form used before invoking factor extraction. -/
theorem eq_onePointMass_of_no_center [Zero K]
    {P : Tensor K (Fin d ⊕ Fin d)} (hP : ThreeLayers P)
    (hPzero : P (fun _ => false) = 0)
    (hc : ∀ x, weight x = d → P x = 0) :
    P = onePointMass (P (fun _ => true)) := by
  classical
  funext x
  by_cases hx : x = (fun _ => true)
  · simp [onePointMass, hx]
  · simp only [onePointMass, ite_eq_right hx]
    by_contra hn
    rcases hP x hn with h | h | h
    · have he := (weight_eq_zero_iff x).mp h
      exact hn (he ▸ hPzero)
    · exact hn (hc x h)
    · exact hx ((weight_eq_card_iff x).mp (by simpa [Fintype.card_sum, two_mul] using h))

/-- Three-layer support is unchanged by a permutation of the two-block ports. -/
theorem ThreeLayers.reindex [Zero K] {f : Tensor K (Fin d ⊕ Fin d)}
    (hf : ThreeLayers f) (e : Equiv.Perm (Fin d ⊕ Fin d)) :
    ThreeLayers (Tensor.reindex e f) := by
  intro x hx
  simpa only [weight_reindex] using hf _ hx

/-- The two-central-parts construction includes the existence of the required
port permutations; the inputs need not already use canonical central words. -/
theorem exists_joinX_isMountain [CommSemiring K] [NoZeroDivisors K]
    {P N : Tensor K (Fin d ⊕ Fin d)}
    (hd : 0 < d) (hP : ThreeLayers P) (hN : ThreeLayers N)
    (hPzero : P (fun _ => false) = 0) (hNone : N (fun _ => true) = 0)
    (hPone : P (fun _ => true) ≠ 0) (hNzero : N (fun _ => false) ≠ 0)
    (hPc : ∃ x, P x ≠ 0 ∧ weight x = d)
    (hNc : ∃ x, N x ≠ 0 ∧ weight x = d)
    (hPd : Tensor.HalfChargeDivisible P d) (hNd : Tensor.HalfChargeDivisible N d) :
    ∃ eP eN : Equiv.Perm (Fin d ⊕ Fin d),
      IsMountain (Tensor.reindex (blockEquiv d)
        (joinX (Tensor.reindex eP P) (Tensor.reindex eN N))) := by
  obtain ⟨x, hx, hwx⟩ := hPc
  obtain ⟨y, hy, hwy⟩ := hNc
  obtain ⟨eP, heP⟩ := exists_reindex_evaluation P x
    (Sum.elim (fun _ => false) (fun _ => true)) (by simp [weight_sum, hwx])
  obtain ⟨eN, heN⟩ := exists_reindex_evaluation N y
    (Sum.elim (fun _ => true) (fun _ => false)) (by simp [weight_sum, hwy])
  refine ⟨eP, eN, joinX_isMountain hd (hP.reindex eP) (hN.reindex eN)
    hPzero hNone hPone hNzero ?_ ?_
    (Tensor.reindex_halfChargeDivisible eP hPd)
    (Tensor.reindex_halfChargeDivisible eN hNd)⟩
  · rwa [heP]
  · rwa [heN]

/-- The explicit finite menu of table constructions used after the two
opposite endpoints have been obtained. Each constructor names its actual
coefficient operation; this is not an abstract accessibility predicate. -/
inductive PairGadget [CommSemiring K] (P N : Tensor K (Fin d ⊕ Fin d)) :
    Tensor K (Fin d ⊕ Fin d) → Prop where
  | useLeft : PairGadget P N P
  | useRight : PairGadget P N N
  | join (eP eN : Equiv.Perm (Fin d ⊕ Fin d)) :
      PairGadget P N (joinX (Tensor.reindex eP P) (Tensor.reindex eN N))
  | doubleLeft (eP : Equiv.Perm (Fin d ⊕ Fin d)) :
      PairGadget P N (joinTwoCopiesX (Tensor.reindex eP P) N)
  | doubleRight (eN : Equiv.Perm (Fin d ⊕ Fin d)) :
      PairGadget P N (joinTwoCopiesX (Tensor.reindex eN N) P)

/-- Complete coefficient-level case analysis for the latter half of the
Section 4 proof: from the two opposite surviving endpoints, one of the listed
concrete connectors is a mountain, or the original tables are pure opposite
point masses. The latter conclusion does not assert unary factor extraction. -/
theorem endpoint_pair_mountain_or_pure [CommSemiring K] [NoZeroDivisors K]
    {P N : Tensor K (Fin d ⊕ Fin d)}
    (hd : 0 < d) (hP : ThreeLayers P) (hN : ThreeLayers N)
    (hPone : P (fun _ => true) ≠ 0) (hNzero : N (fun _ => false) ≠ 0)
    (hPd : Tensor.HalfChargeDivisible P d) (hNd : Tensor.HalfChargeDivisible N d) :
    (∃ M, PairGadget P N M ∧ IsMountain (Tensor.reindex (blockEquiv d) M)) ∨
      (P = onePointMass (P (fun _ => true)) ∧
        N = zeroPointMass (N (fun _ => false))) := by
  classical
  by_cases hPzero : P (fun _ => false) = 0
  · by_cases hNone : N (fun _ => true) = 0
    · by_cases hPc : ∃ x, P x ≠ 0 ∧ weight x = d
      · by_cases hNc : ∃ x, N x ≠ 0 ∧ weight x = d
        · obtain ⟨eP, eN, hm⟩ := exists_joinX_isMountain hd hP hN hPzero hNone
            hPone hNzero hPc hNc hPd hNd
          exact Or.inl ⟨_, PairGadget.join eP eN, hm⟩
        · have hNpure := eq_zeroPointMass_of_no_center hN hNone
            (fun x hw => by
              by_contra hx
              exact hNc ⟨x, hx, hw⟩)
          obtain ⟨x, hx, hw⟩ := hPc
          obtain ⟨eP, heP⟩ := exists_reindex_evaluation P x
            (Sum.elim (fun _ => false) (fun _ => true)) (by simp [weight_sum, hw])
          refine Or.inl ⟨_, PairGadget.doubleLeft eP, ?_⟩
          rw [hNpure]
          apply joinTwoCopiesX_isMountain (Tensor.reindex eP P) _ hd hNzero hPone
          · rwa [heP]
          · exact Tensor.reindex_halfChargeDivisible _ hPd
      · by_cases hNc : ∃ x, N x ≠ 0 ∧ weight x = d
        · have hPpure := eq_onePointMass_of_no_center hP hPzero
            (fun x hw => by
              by_contra hx
              exact hPc ⟨x, hx, hw⟩)
          obtain ⟨x, hx, hw⟩ := hNc
          obtain ⟨eN, heN⟩ := exists_reindex_evaluation N x
            (Sum.elim (fun _ => true) (fun _ => false)) (by simp [weight_sum, hw])
          refine Or.inl ⟨_, PairGadget.doubleRight eN, ?_⟩
          rw [hPpure]
          apply joinTwoCopiesX_mirror_isMountain (Tensor.reindex eN N) _ hd hPone hNzero
          · rwa [heN]
          · exact Tensor.reindex_halfChargeDivisible _ hNd
        · exact Or.inr ⟨
            eq_onePointMass_of_no_center hP hPzero (fun x hw => by
              by_contra hx
              exact hPc ⟨x, hx, hw⟩),
            eq_zeroPointMass_of_no_center hN hNone (fun x hw => by
              by_contra hx
              exact hNc ⟨x, hx, hw⟩)⟩
    · exact Or.inl ⟨N, PairGadget.useRight,
        isMountain_of_halfChargeDivisible hd
          (Tensor.reindex_halfChargeDivisible _ hNd) hNzero hNone⟩
  · exact Or.inl ⟨P, PairGadget.useLeft,
      isMountain_of_halfChargeDivisible hd
        (Tensor.reindex_halfChargeDivisible _ hPd) hPzero hPone⟩

/-- At twice the height, divisibility alone already forces the three layers
on the two-block port type. -/
theorem threeLayers_of_halfChargeDivisible [Zero K]
    {P : Tensor K (Fin d ⊕ Fin d)} (hd : 0 < d)
    (hP : Tensor.HalfChargeDivisible P d) : ThreeLayers P := by
  intro x hx
  have hb := weight_le_card x
  have hd' : (0 : ℤ) < d := by exact_mod_cast hd
  have hl : -(d : ℤ) ≤ halfCharge x := by
    simp only [halfCharge, Fintype.card_sum, Fintype.card_fin]
    omega
  have hu : halfCharge x ≤ (d : ℤ) := by
    simp only [Fintype.card_sum, Fintype.card_fin] at hb
    simp only [halfCharge, Fintype.card_sum, Fintype.card_fin]
    omega
  have hc := eq_neg_or_zero_or_pos_of_dvd_of_bounds hd' (hP x hx) hl hu
  simp only [halfCharge, Fintype.card_sum, Fintype.card_fin] at hc
  omega

/-- A minimal-hypothesis interface to the complete endpoint-pair construction. -/
theorem endpoint_pair_mountain_or_pure_of_divisible [CommSemiring K] [NoZeroDivisors K]
    {P N : Tensor K (Fin d ⊕ Fin d)}
    (hd : 0 < d)
    (hPone : P (fun _ => true) ≠ 0) (hNzero : N (fun _ => false) ≠ 0)
    (hPd : Tensor.HalfChargeDivisible P d) (hNd : Tensor.HalfChargeDivisible N d) :
    (∃ M, PairGadget P N M ∧ IsMountain (Tensor.reindex (blockEquiv d) M)) ∨
      (P = onePointMass (P (fun _ => true)) ∧
        N = zeroPointMass (N (fun _ => false))) :=
  endpoint_pair_mountain_or_pure hd (threeLayers_of_halfChargeDivisible hd hPd)
    (threeLayers_of_halfChargeDivisible hd hNd) hPone hNzero hPd hNd

end MountainConstruction

end Paper2
