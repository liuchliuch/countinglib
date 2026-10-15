import Paper2.Charge
import Mathlib.Tactic

/-!
# Endpoint-preserving native-X self-loops

This file proves the cancellation argument directly over coefficient tables.
Every contraction below is an actual two-term native-disequality contraction;
no endpoint-existence or external-literature lemma is assumed.
-/

set_option linter.unusedSimpArgs false

namespace Paper2
namespace EndpointSelfLoop

variable {K : Type*} {ι κ ν : Type}

/-- The exact surviving port occurrences after deleting two distinct ports. -/
def Remaining (a b : ι) := {i : ι // i ≠ a ∧ i ≠ b}

noncomputable instance [Fintype ι] (a b : ι) : Fintype (Remaining a b) :=
by
  classical
  unfold Remaining
  infer_instance

/-- A concrete bijection exposing the deleted ports as the two ends of an edge.
`false` names `a` and `true` names `b`. -/
noncomputable def splitPorts (a b : ι) (hab : a ≠ b) :
    ι ≃ (Remaining a b ⊕ Bool) := by
  classical
  refine {
    toFun := fun i => if ha : i = a then .inr false else
      if hb : i = b then .inr true else .inl ⟨i, ha, hb⟩
    invFun := Sum.elim Subtype.val (fun c => if c then b else a)
    left_inv := ?_
    right_inv := ?_ }
  · intro i
    by_cases ha : i = a
    · simp [Sum.elim, ha]
    · by_cases hb : i = b <;> simp [Sum.elim, ha, hb, Ne.symm hab]
  · intro i
    rcases i with i | c
    · simp [Sum.elim, i.property.1, i.property.2]
      rfl
    · cases c <;> simp [Sum.elim, hab, Ne.symm hab]

/-- The assignment left on the undeleted occurrences. -/
def restrict (a b : ι) (x : ι → Bool) : Remaining a b → Bool :=
  fun i => x i.val

/-- A genuine self-loop, including the summation over its two allowed states. -/
noncomputable def loop [AddCommMonoid K] (a b : ι) (hab : a ≠ b)
    (f : Tensor K ι) : Tensor K (Remaining a b) :=
  Tensor.contractX (Tensor.reindex (splitPorts a b hab) f)

/-- Reinsert one of the two native-X edge states. -/
noncomputable def extendPair (a b : ι) (hab : a ≠ b)
    (x : Remaining a b → Bool) (t : Bool) : ι → Bool :=
  fun i => Sum.elim x (fun c : Bool => if c then !t else t) (splitPorts a b hab i)

 theorem extendPair_restrict (a b : ι) (hab : a ≠ b)
    (x : ι → Bool) (h : x b = !(x a)) :
    extendPair a b hab (restrict a b x) (x a) = x := by
  classical
  funext i
  by_cases ha : i = a
  · subst i
    simp [Sum.elim, extendPair, splitPorts]
  · by_cases hb : i = b
    · subst i
      simp [Sum.elim, extendPair, splitPorts, hab, Ne.symm hab, h]
    · simp [Sum.elim, extendPair, splitPorts, ha, hb, restrict]

 theorem extendPair_restrict_swap [DecidableEq ι] (a b : ι) (hab : a ≠ b)
    (x : ι → Bool) (h : x b = !(x a)) :
    extendPair a b hab (restrict a b x) (!(x a)) =
      (fun i => x (Equiv.swap a b i)) := by
  classical
  funext i
  by_cases ha : i = a
  · subst i
    simp [Sum.elim, extendPair, splitPorts, h]
  · by_cases hb : i = b
    · subst i
      simp [Sum.elim, extendPair, splitPorts, hab, Ne.symm hab, h]
    · simp [Sum.elim, extendPair, splitPorts, ha, hb, restrict,
        Equiv.swap_apply_of_ne_of_ne ha hb]

/-- The deleted-port convention agrees exactly with the original and transposed
word contributions. Thus no summand is normalized or discarded. -/
theorem loop_apply_restrict [AddCommMonoid K] [DecidableEq ι]
    (a b : ι) (hab : a ≠ b) (f : Tensor K ι)
    (x : ι → Bool) (h : x b = !(x a)) :
    loop a b hab f (restrict a b x) =
      f x + f (fun i => x (Equiv.swap a b i)) := by
  change (∑ t : Bool, f (extendPair a b hab (restrict a b x) t)) = _
  have hs : (∑ t : Bool, f (extendPair a b hab (restrict a b x) t)) =
      f (extendPair a b hab (restrict a b x) (x a)) +
      f (extendPair a b hab (restrict a b x) (!(x a))) := by
    cases x a <;> simp [Fintype.sum_bool, add_comm]
  rw [hs, extendPair_restrict a b hab x h, extendPair_restrict_swap a b hab x h]

/-- The only scalar obstruction to the odd-cycle argument is characteristic 2. -/
theorem triangle_nonzero [CommRing K] [NoZeroDivisors K]
    (h2 : (2 : K) ≠ 0) (A B C : K) (hA : A ≠ 0) :
    A + B ≠ 0 ∨ A + C ≠ 0 ∨ B + C ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨hab, hac, hbc⟩ := h
  have htwice : (2 : K) * A = 0 := by
    linear_combination hab + hac - hbc
  exact mul_ne_zero h2 hA htwice

/-- With two equal true bits and one false bit, the three swapped words form
an actual triangle in the disequality-contraction graph. -/
theorem swap_triangle [DecidableEq ι] (x : ι → Bool) (a b c : ι)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : x a = true) (hb : x b = true) (hc : x c = false) :
    (fun i => x (Equiv.swap a c (Equiv.swap a b i))) =
      (fun i => x (Equiv.swap b c i)) := by
  funext i
  by_cases hia : i = a
  · subst i
    simp [Equiv.swap_apply_def, hab, Ne.symm hab, hac, Ne.symm hac,
      hbc, Ne.symm hbc, ha, hb, hc]
  · by_cases hib : i = b
    · subst i
      simp [Equiv.swap_apply_def, hab, Ne.symm hab, hac, Ne.symm hac,
        hbc, Ne.symm hbc, ha, hb, hc]
    · by_cases hic : i = c
      · subst i
        simp [Equiv.swap_apply_def, hab, Ne.symm hab, hac, Ne.symm hac,
          hbc, Ne.symm hbc, ha, hb, hc]
      · simp [Equiv.swap_apply_def, hia, hib, hic]

/-- The deletion API removes exactly two occurrences, even for a self-loop. -/
theorem remaining_card [Fintype ι] (a b : ι) (hab : a ≠ b) :
    Fintype.card (Remaining a b) + 2 = Fintype.card ι := by
  classical
  simpa using (Fintype.card_congr (splitPorts a b hab)).symm

/-- An inserted disequality pair has net charge zero. -/
theorem doubledCharge_extendPair [Fintype ι] (a b : ι) (hab : a ≠ b)
    (y : Remaining a b → Bool) (t : Bool) :
    doubledCharge (extendPair a b hab y t) = doubledCharge y := by
  classical
  exact (doubledCharge_reindex (splitPorts a b hab) _).trans (doubledCharge_X_pair y t)

/-- Deleting opposite bits preserves the selected word's charge exactly. -/
theorem doubledCharge_restrict [Fintype ι] (a b : ι) (hab : a ≠ b)
    (x : ι → Bool) (h : x b = !(x a)) :
    doubledCharge (restrict a b x) = doubledCharge x := by
  classical
  have he := doubledCharge_extendPair a b hab (restrict a b x) (x a)
  rw [extendPair_restrict a b hab x h] at he
  exact he.symm

/-- Strict positive charge away from the all-one endpoint supplies two one
ports and one zero port; no coordinate-selection hypothesis is imported. -/
theorem exists_true_true_false [Fintype ι] (x : ι → Bool)
    (hpos : 0 < doubledCharge x) (hend : x ≠ fun _ => true) :
    ∃ a b c : ι, a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
      x a = true ∧ x b = true ∧ x c = false := by
  classical
  have hwlt : weight x < Fintype.card ι := by
    have hwle := weight_le_card x
    have hwne := mt (weight_eq_card_iff x).mp hend
    omega
  have hw2 : 1 < weight x := by
    unfold doubledCharge at hpos
    omega
  let s : Finset ι := Finset.univ.filter (fun i => x i = true)
  have hs : s.card = weight x := by
    simp only [s, Finset.card_filter, weight]
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
  have hat : x a = true := (Finset.mem_filter.mp ha).2
  have hbt : x b = true := (Finset.mem_filter.mp hb).2
  obtain ⟨c, hcf⟩ : ∃ c, x c = false := by
    by_contra h
    push Not at h
    apply hend
    funext i
    cases hi : x i
    · exact False.elim (h i hi)
    · rfl
  refine ⟨a, b, c, hab, ?_, ?_, hat, hbt, hcf⟩
  · intro hac
    subst c
    simp_all
  · intro hbc
    subst c
    simp_all

/-- The actual one-step endpoint-preserving contraction. The chosen pair can
change when one apparent contraction cancels: the three possibilities cannot
all cancel in characteristic different from two. -/
theorem exists_preserving_loop [Fintype ι] [CommRing K] [NoZeroDivisors K]
    (h2 : (2 : K) ≠ 0) (f : Tensor K ι) (x : ι → Bool)
    (hx : f x ≠ 0) (hpos : 0 < doubledCharge x) (hend : x ≠ fun _ => true) :
    ∃ (a b : ι) (hab : a ≠ b) (y : Remaining a b → Bool),
      loop a b hab f y ≠ 0 ∧ doubledCharge y = doubledCharge x := by
  classical
  obtain ⟨a, b, c, hab, hac, hbc, ha, hb, hc⟩ := exists_true_true_false x hpos hend
  let y : ι → Bool := fun i => x (Equiv.swap a c i)
  let z : ι → Bool := fun i => x (Equiv.swap b c i)
  have hxac : x c = !(x a) := by simp [ha, hc]
  have hxbc : x c = !(x b) := by simp [hb, hc]
  have hyab : y b = !(y a) := by
    simp [y, Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) hbc, hb, hc]
  have hswap : (fun i => y (Equiv.swap a b i)) = z :=
    swap_triangle x a b c hab hac hbc ha hb hc
  rcases triangle_nonzero h2 (f x) (f y) (f z) hx with hxy | hxz | hyz
  · refine ⟨a, c, hac, restrict a c x, ?_, doubledCharge_restrict a c hac x hxac⟩
    simpa only [loop_apply_restrict a c hac f x hxac] using hxy
  · refine ⟨b, c, hbc, restrict b c x, ?_, doubledCharge_restrict b c hbc x hxbc⟩
    simpa only [loop_apply_restrict b c hbc f x hxbc] using hxz
  · refine ⟨a, b, hab, restrict a b y, ?_, ?_⟩
    · simpa only [loop_apply_restrict a b hab f y hyab, hswap] using hyz
    · exact (doubledCharge_restrict a b hab y hyab).trans
        (doubledCharge_reindex (Equiv.swap a c) x)

/-- A finite derivation consisting solely of port permutations and genuine
native-X self-loops. There is no arbitrary replacement or scalar-normalization
constructor. The intermediate tensors retain their full coefficient tables. -/
inductive Reachable (K : Type*) [AddCommMonoid K] :
    {ι κ : Type} → Tensor K ι → Tensor K κ → Prop
  | refl {ι : Type} (f : Tensor K ι) : Reachable K f f
  | reindex {ι κ : Type} (e : ι ≃ κ) (f : Tensor K ι) :
      Reachable K f (Tensor.reindex e f)
  | selfLoop {ι : Type} (f : Tensor K (ι ⊕ Bool)) :
      Reachable K f (Tensor.contractX f)
  | trans {ι κ ν : Type} {f : Tensor K ι} {g : Tensor K κ} {h : Tensor K ν} :
      Reachable K f g → Reachable K g h → Reachable K f h

theorem reachable_loop [AddCommMonoid K] (a b : ι) (hab : a ≠ b)
    (f : Tensor K ι) : Reachable K f (loop a b hab f) :=
  .trans (.reindex (splitPorts a b hab) f) (.selfLoop _)

/-- The two-state implementation is exactly contraction against the native
binary disequality matrix, including both zero and both nonzero entries. -/
theorem contractX_eq_disequality_sum [Semiring K]
    (f : Tensor K (ι ⊕ Bool)) (x : ι → Bool) :
    Tensor.contractX f x = ∑ a : Bool, ∑ b : Bool,
      Signature.disequality a b *
        f (Sum.elim x (fun c : Bool => if c then b else a)) := by
  simp [Tensor.contractX, Signature.disequality, Fintype.sum_bool, add_comm]

/-- A family genuinely closed under these two allowed operations contains
every table reached by the finite derivation. This separates the algebraic
lemma from whichever closure/reduction convention a later application uses. -/
theorem Reachable.closed [AddCommMonoid K]
    (C : (ι : Type) → Tensor K ι → Prop)
    (hperm : ∀ {ι κ : Type} (e : ι ≃ κ) (f : Tensor K ι),
      C ι f → C κ (Tensor.reindex e f))
    (hloop : ∀ {ι : Type} (f : Tensor K (ι ⊕ Bool)),
      C (ι ⊕ Bool) f → C ι (Tensor.contractX f))
    {f : Tensor K ι} {g : Tensor K κ} (h : Reachable K f g)
    (hf : C ι f) : C κ g := by
  induction h with
  | refl f => exact hf
  | reindex e f => exact hperm e f hf
  | selfLoop f => exact hloop f hf
  | trans h₁ h₂ ih₁ ih₂ => exact ih₂ (ih₁ hf)

/-- No finite sequence can acquire infinitely many port occurrences. -/
theorem Reachable.finite [AddCommMonoid K] {f : Tensor K ι} {g : Tensor K κ}
    (h : Reachable K f g) : ∀ [Finite ι], Finite κ := by
  induction h with
  | refl f => intro _; infer_instance
  | reindex e f => intro _; exact Finite.of_equiv _ e
  | selfLoop f =>
    intro _
    exact Finite.of_injective (Sum.inl : _ → _ ⊕ Bool) Sum.inl_injective
  | trans h₁ h₂ ih₁ ih₂ =>
    intro _
    let := ih₁
    exact ih₂

/-- Every permitted step preserves the full supported half-charge lattice,
not merely the one word used to choose the next contraction. -/
theorem Reachable.halfChargeDivisible [AddCommMonoid K]
    {f : Tensor K ι} {g : Tensor K κ} (h : Reachable K f g) (d : ℤ) :
    ∀ [Fintype ι] [Fintype κ],
      Tensor.HalfChargeDivisible f d → Tensor.HalfChargeDivisible g d := by
  induction h with
  | refl f =>
    intro F G hf
    have hFG : F = G := Subsingleton.elim _ _
    cases hFG
    exact hf
  | reindex e f => intro _ _ hf; exact Tensor.reindex_halfChargeDivisible e hf
  | @selfLoop ι f =>
    intro F G hf
    have hFG : F = @instFintypeSum ι Bool G inferInstance := Subsingleton.elim _ _
    cases hFG
    exact Tensor.contractX_halfChargeDivisible hf
  | @trans ι κ ν f g h h₁ h₂ ih₁ ih₂ =>
    intro _ _ hf
    let : Finite κ := h₁.finite
    let : Fintype κ := Fintype.ofFinite κ
    exact ih₂ (ih₁ hf)

/-- The derivation deletes exactly two ports per self-loop. The existential
count is built recursively from the actual derivation constructors. -/
theorem Reachable.arity [AddCommMonoid K]
    {f : Tensor K ι} {g : Tensor K κ} (h : Reachable K f g) :
    ∀ [Fintype ι] [Fintype κ], ∃ r : ℕ,
      Fintype.card ι = Fintype.card κ + 2 * r := by
  induction h with
  | refl f =>
    intro F G
    have hFG : F = G := Subsingleton.elim _ _
    cases hFG
    exact ⟨0, by omega⟩
  | reindex e f => intro _ _; exact ⟨0, by simpa using Fintype.card_congr e⟩
  | @selfLoop ι f =>
    intro F G
    have hFG : F = @instFintypeSum ι Bool G inferInstance := Subsingleton.elim _ _
    cases hFG
    exact ⟨1, by simp⟩
  | @trans ι κ ν f g h h₁ h₂ ih₁ ih₂ =>
    intro _ _
    let : Finite κ := h₁.finite
    let : Fintype κ := Fintype.ofFinite κ
    obtain ⟨r, hr⟩ := ih₁
    obtain ⟨s, hs⟩ := ih₂
    exact ⟨r + s, by omega⟩

/-- Strong induction actually executes the reduction until every surviving
bit is one. Positive doubled charge `m` therefore yields arity exactly `m`. -/
theorem positive_endpoint [Fintype ι] [CommRing K] [NoZeroDivisors K]
    (h2 : (2 : K) ≠ 0) (f : Tensor K ι) (x : ι → Bool)
    (hx : f x ≠ 0) {m : ℕ} (hm : 0 < m)
    (hc : doubledCharge x = (m : ℤ)) :
    ∃ g : Signature K m, Reachable K f g ∧ g (fun _ => true) ≠ 0 := by
  classical
  generalize hn : Fintype.card ι = n
  induction n using Nat.strong_induction_on generalizing ι with
  | h n ih =>
    by_cases hend : x = fun _ => true
    · have hcard : Fintype.card ι = m := by
        rw [hend] at hc
        simp only [doubledCharge, weight_true] at hc
        omega
      let e : ι ≃ Fin m := Fintype.equivOfCardEq (by simpa using hcard)
      refine ⟨Tensor.reindex e f, .reindex e f, ?_⟩
      change f (fun _ => true) ≠ 0
      simpa only [hend] using hx
    · have hpos : 0 < doubledCharge x := by omega
      obtain ⟨a, b, hab, y, hy, hcharge⟩ := exists_preserving_loop h2 f x hx hpos hend
      have hlt : Fintype.card (Remaining a b) < n := by
        have := remaining_card a b hab
        omega
      obtain ⟨g, hg, hgne⟩ := ih (Fintype.card (Remaining a b)) hlt
        (loop a b hab f) y hy (hcharge.trans hc) rfl
      exact ⟨g, .trans (reachable_loop a b hab f) hg, hgne⟩

/-- The Section 4 positive endpoint conclusion, in the paper's half-charge
normalization. Only a supported word, even input arity, and `d > 0` are assumed. -/
theorem positive_halfCharge_endpoint [Fintype ι] [CommRing K] [NoZeroDivisors K]
    (h2 : (2 : K) ≠ 0) (f : Tensor K ι) (x : ι → Bool)
    (hx : f x ≠ 0) (heven : Even (Fintype.card ι)) {d : ℕ} (hd : 0 < d)
    (hc : halfCharge x = (d : ℤ)) :
    ∃ g : Signature K (2 * d), Reachable K f g ∧ g (fun _ => true) ≠ 0 := by
  apply positive_endpoint h2 f x hx (by omega : 0 < 2 * d)
  rw [← twice_halfCharge heven x, hc]
  norm_cast

/-- Simultaneously complement every boundary bit. Used only to prove the
negative-charge theorem; it is not an extra constructor of `Reachable`. -/
def flip (f : Tensor K ι) : Tensor K ι := fun x => f (fun i => !(x i))

@[simp] theorem flip_flip (f : Tensor K ι) : flip (flip f) = f := by
  funext x
  simp [flip]

 theorem flip_reindex (e : ι ≃ κ) (f : Tensor K ι) :
    flip (Tensor.reindex e f) = Tensor.reindex e (flip f) := rfl

 theorem flip_contractX [AddCommMonoid K] (f : Tensor K (ι ⊕ Bool)) :
    flip (Tensor.contractX f) = Tensor.contractX (flip f) := by
  funext x
  simp only [flip, Tensor.contractX, Fintype.sum_bool]
  rw [add_comm]
  congr 1 <;> congr 1 <;> funext i <;> rcases i with i | c
  · rfl
  · cases c <;> rfl
  · rfl
  · cases c <;> rfl

/-- Complementing every coefficient table transports a derivation without
introducing any bit-flip gadget: its steps remain the same permutations and X
self-loops. -/
theorem Reachable.complement [AddCommMonoid K] {f : Tensor K ι} {g : Tensor K κ}
    (h : Reachable K f g) : Reachable K (flip f) (flip g) := by
  induction h with
  | refl f => exact .refl _
  | reindex e f => simpa only [flip_reindex] using Reachable.reindex e (flip f)
  | selfLoop f => simpa only [flip_contractX] using Reachable.selfLoop (flip f)
  | trans h₁ h₂ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- Negative supported doubled charge yields a genuine all-zero endpoint by
the same finite self-loop construction. No complement operation is added to
the permitted output sequence. -/
theorem negative_endpoint [Fintype ι] [CommRing K] [NoZeroDivisors K]
    (h2 : (2 : K) ≠ 0) (f : Tensor K ι) (x : ι → Bool)
    (hx : f x ≠ 0) {m : ℕ} (hm : 0 < m)
    (hc : doubledCharge x = -(m : ℤ)) :
    ∃ g : Signature K m, Reachable K f g ∧ g (fun _ => false) ≠ 0 := by
  have hflip : flip f (fun i => !(x i)) ≠ 0 := by simpa [flip] using hx
  have hcflip : doubledCharge (fun i => !(x i)) = (m : ℤ) := by
    rw [doubledCharge_complement, hc]
    omega
  obtain ⟨g, hg, hgne⟩ := positive_endpoint h2 (flip f) _ hflip hm hcflip
  refine ⟨flip g, ?_, ?_⟩
  · simpa only [flip_flip] using hg.complement
  · simpa only [flip, Bool.not_false] using hgne

/-- The Section 4 negative endpoint conclusion in half-charge normalization. -/
theorem negative_halfCharge_endpoint [Fintype ι] [CommRing K] [NoZeroDivisors K]
    (h2 : (2 : K) ≠ 0) (f : Tensor K ι) (x : ι → Bool)
    (hx : f x ≠ 0) (heven : Even (Fintype.card ι)) {d : ℕ} (hd : 0 < d)
    (hc : halfCharge x = -(d : ℤ)) :
    ∃ g : Signature K (2 * d), Reachable K f g ∧ g (fun _ => false) ≠ 0 := by
  apply negative_endpoint h2 f x hx (by omega : 0 < 2 * d)
  rw [← twice_halfCharge heven x, hc]
  push_cast
  ring

/-- Positive endpoint extraction also preserves every input support-lattice
restriction, which is the further fact used immediately in Section 4. -/
theorem positive_halfCharge_endpoint_divisible [Fintype ι]
    [CommRing K] [NoZeroDivisors K]
    (h2 : (2 : K) ≠ 0) (f : Tensor K ι) (x : ι → Bool)
    (hx : f x ≠ 0) (heven : Even (Fintype.card ι)) {d : ℕ} (hd : 0 < d)
    (hc : halfCharge x = (d : ℤ)) (hf : Tensor.HalfChargeDivisible f d) :
    ∃ g : Signature K (2 * d), Reachable K f g ∧ g (fun _ => true) ≠ 0 ∧
      Tensor.HalfChargeDivisible g d := by
  obtain ⟨g, hg, hgne⟩ := positive_halfCharge_endpoint h2 f x hx heven hd hc
  exact ⟨g, hg, hgne, hg.halfChargeDivisible d hf⟩

/-- Negative endpoint extraction with its full support-lattice restriction. -/
theorem negative_halfCharge_endpoint_divisible [Fintype ι]
    [CommRing K] [NoZeroDivisors K]
    (h2 : (2 : K) ≠ 0) (f : Tensor K ι) (x : ι → Bool)
    (hx : f x ≠ 0) (heven : Even (Fintype.card ι)) {d : ℕ} (hd : 0 < d)
    (hc : halfCharge x = -(d : ℤ)) (hf : Tensor.HalfChargeDivisible f d) :
    ∃ g : Signature K (2 * d), Reachable K f g ∧ g (fun _ => false) ≠ 0 ∧
      Tensor.HalfChargeDivisible g d := by
  obtain ⟨g, hg, hgne⟩ := negative_halfCharge_endpoint h2 f x hx heven hd hc
  exact ⟨g, hg, hgne, hg.halfChargeDivisible d hf⟩

end EndpointSelfLoop
end Paper2
