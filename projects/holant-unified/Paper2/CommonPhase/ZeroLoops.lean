import Paper2.EndpointSelfLoop

/-! Source Lemma 8.3: injectivity of all native-X contractions on EO tensors. -/
namespace Paper2.CommonPhase
open EndpointSelfLoop
variable {K : Type*} {ι : Type}

/-- There is a third occurrence outside two specified ports. -/
theorem exists_third [Fintype ι] (hn : 3 ≤ Fintype.card ι) (a b : ι) :
    ∃ c, c ≠ a ∧ c ≠ b := by
  classical
  by_contra h
  push Not at h
  have hs : (Finset.univ : Finset ι) ⊆ {a, b} := by
    intro c hc
    by_cases ha : c = a
    · simp [ha]
    · simp [h c ha]
  have hc := Finset.card_le_card hs
  have hp : ({a, b} : Finset ι).card ≤ 2 := Finset.card_le_two
  simp only [Finset.card_univ] at hc
  omega

/-- The three linear equations force a mixed word's coefficient to zero. -/
theorem coefficient_zero_of_three [CommRing K] [NoZeroDivisors K]
    [DecidableEq ι] (h2 : (2 : K) ≠ 0) (f : Tensor K ι)
    (hz : ∀ a b (h : a ≠ b), loop a b h f = 0)
    (x : ι → Bool) (a b c : ι)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : x a = true) (hb : x b = true) (hc : x c = false) : f x = 0 := by
  by_contra hnz
  let y : ι → Bool := fun i => x (Equiv.swap a c i)
  let z : ι → Bool := fun i => x (Equiv.swap b c i)
  have hxac : x c = !(x a) := by simp [ha, hc]
  have hxbc : x c = !(x b) := by simp [hb, hc]
  have hyab : y b = !(y a) := by
    simp [y, Equiv.swap_apply_of_ne_of_ne (Ne.symm hab) hbc, hb, hc]
  have hswap : (fun i => y (Equiv.swap a b i)) = z :=
    swap_triangle x a b c hab hac hbc ha hb hc
  have hxy : f x + f y = 0 := by
    simpa only [loop_apply_restrict a c hac f x hxac, Pi.zero_apply] using
      congrFun (hz a c hac) (restrict a c x)
  have hxz : f x + f z = 0 := by
    simpa only [loop_apply_restrict b c hbc f x hxbc, Pi.zero_apply] using
      congrFun (hz b c hbc) (restrict b c x)
  have hyz : f y + f z = 0 := by
    simpa only [loop_apply_restrict a b hab f y hyab, hswap, Pi.zero_apply] using
      congrFun (hz a b hab) (restrict a b y)
  rcases triangle_nonzero h2 (f x) (f y) (f z) hnz with h | h | h
  · exact h hxy
  · exact h hxz
  · exact h hyz

/-- Complementing the output word commutes with native-X contraction. -/
theorem loop_complement [AddCommMonoid K] (a b : ι) (hab : a ≠ b)
    (f : Tensor K ι) (x : Remaining a b → Bool) :
    loop a b hab (fun y => f (fun i => !(y i))) x =
      loop a b hab f (fun i => !(x i)) := by
  classical
  have he (t : Bool) :
      (fun i => !(extendPair a b hab x t i)) =
        extendPair a b hab (fun i => !(x i)) (!t) := by
    funext i
    simp only [extendPair]
    cases splitPorts a b hab i with
    | inl j => rfl
    | inr q => cases q <;> simp
  change (∑ t : Bool, f (fun i => !(extendPair a b hab x t i))) =
    ∑ t : Bool, f (extendPair a b hab (fun i => !(x i)) t)
  simp only [he, Fintype.sum_bool, Bool.not_false, Bool.not_true]
  exact add_comm _ _

/-- The actual Lemma 8.3, with no assumption on endpoint coefficients. -/
theorem vanishing_pair_contractions [Fintype ι] [CommRing K] [NoZeroDivisors K]
    (h2 : (2 : K) ≠ 0) (hn : 3 ≤ Fintype.card ι) (f : Tensor K ι)
    (hz : ∀ a b (h : a ≠ b), loop a b h f = 0)
    (x : ι → Bool) (hx0 : x ≠ fun _ => false) (hx1 : x ≠ fun _ => true) :
    f x = 0 := by
  classical
  obtain ⟨a, ha⟩ : ∃ a, x a = true := by
    by_contra h
    push Not at h
    apply hx0
    funext i
    cases hi : x i <;> simp_all
  obtain ⟨c, hc⟩ : ∃ c, x c = false := by
    by_contra h
    push Not at h
    apply hx1
    funext i
    cases hi : x i <;> simp_all
  have hac : a ≠ c := by intro h; subst c; simp_all
  obtain ⟨b, hba, hbc⟩ := exists_third hn a c
  cases hb : x b with
  | true => exact coefficient_zero_of_three h2 f hz x a b c hba.symm hac hbc ha hb hc
  | false =>
    let g : Tensor K ι := fun y => f (fun i => !(y i))
    have hgz : ∀ u v (h : u ≠ v), loop u v h g = 0 := by
      intro u v h
      funext y
      change loop u v h (fun z => f (fun i => !(z i))) y = 0
      rw [loop_complement, hz]
      rfl
    have hh := coefficient_zero_of_three h2 g hgz (fun i => !(x i)) c b a
      hbc.symm hac.symm hba (by simp [hc]) (by simp [hb]) (by simp [ha])
    simpa [g] using hh

/-- The original Hamming-weight formulation of source Lemma 8.3. -/
theorem vanishing_pair_contractions_weight [Fintype ι] [CommRing K] [NoZeroDivisors K]
    (h2 : (2 : K) ≠ 0) (hn : 3 ≤ Fintype.card ι) (f : Tensor K ι)
    (hz : ∀ a b (h : a ≠ b), loop a b h f = 0)
    (x : ι → Bool) (hlo : 0 < weight x) (hhi : weight x < Fintype.card ι) : f x = 0 := by
  apply vanishing_pair_contractions h2 hn f hz x
  · intro h
    have := (weight_eq_zero_iff x).mpr h
    omega
  · intro h
    have := (weight_eq_card_iff x).mpr h
    omega

/-- EO tensors are determined by their actual pair contractions. -/
theorem eo_zero_of_vanishing_pair_contractions [Fintype ι] [CommRing K]
    [NoZeroDivisors K] (h2 : (2 : K) ≠ 0) (hn : 3 ≤ Fintype.card ι)
    (f : Tensor K ι) (heo : Tensor.ChargeLayer f 0)
    (hz : ∀ a b (h : a ≠ b), loop a b h f = 0) : f = 0 := by
  funext x
  by_cases hx : f x = 0
  · exact hx
  have hc := heo x hx
  have hx0 : x ≠ fun _ => false := by
    intro he
    rw [he] at hc
    simp only [doubledCharge, weight_false, Nat.cast_zero, mul_zero, zero_sub,
      neg_eq_zero, Nat.cast_eq_zero] at hc
    omega
  have hx1 : x ≠ fun _ => true := by
    intro he
    rw [he] at hc
    simp only [doubledCharge, weight_true] at hc
    have : Fintype.card ι = 0 := by omega
    omega
  exact vanishing_pair_contractions h2 hn f hz x hx0 hx1

end Paper2.CommonPhase
