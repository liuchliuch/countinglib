import Paper2.CommonPhase.Phase
import Paper2.CommonPhase.Recovery

/-!
# Paper 2, Lemmas 8.3 and 8.6

The entire argument uses actual native-X finite-sum contractions. The phase
comparison is obtained from a nonzero double-contraction coefficient (one or
two), and not assumed as part of the deck. The final scalar belongs to the
actual algebraic-complex subfield whenever the input and deck do.
-/
namespace Paper2.CommonPhase
open EndpointSelfLoop
variable {ι : Type} {K L : Type*}

theorem loop_div [Field K] (a b : ι) (hab : a ≠ b) (F : Tensor K ι) (c : K)
    (y : Remaining a b → Bool) :
    loop a b hab (fun x => F x / c) y = loop a b hab F y / c := by
  change (∑ t : Bool, F (extendPair a b hab y t) / c) =
    (∑ t : Bool, F (extendPair a b hab y t)) / c
  simp only [div_eq_mul_inv, Finset.sum_mul]

/-- Fixing any one deck coefficient gives positive-real coefficients for the
complete normalized deck. -/
theorem normalized_deck_positive [Fintype ι] (hn : 6 ≤ Fintype.card ι)
    {F : Tensor ℂ ι} {lam : PortPair ι → ℂ}
    {P : (e : PortPair ι) → XMatching (Remaining e.first e.second)}
    (hd : MatchingDeck F lam P) (hnz : ∀ e, lam e ≠ 0) (e₀ : PortPair ι) :
    ∀ e, ∃ r : ℝ, 0 < r ∧ lam e / lam e₀ = (r : ℂ) ∧
      loop e.first e.second e.distinct (fun x => F x / lam e₀) =
        fun y => (r : ℂ) * literal (P e) ℂ y := by
  intro e
  obtain ⟨r, hr, he⟩ := matching_deck_positive hn hd hnz e e₀
  have hr' : lam e / lam e₀ = (r : ℂ) := by rw [he]; exact mul_div_cancel_right₀ _ (hnz e₀)
  refine ⟨r, hr, hr', ?_⟩
  funext y
  rw [loop_div, hd]
  change lam e * literal (P e) ℂ y / lam e₀ = _
  rw [mul_div_right_comm, hr']

/-- The full algebraic conclusion of source Lemma 8.6 over complex coefficients.
Evenness need not be assumed separately; the literal matching deck already
carries all residual pairing data. -/
theorem common_phase_at [Fintype ι] (hn : 6 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (heo : Tensor.ChargeLayer F 0)
    (lam : PortPair ι → ℂ)
    (P : (e : PortPair ι) → XMatching (Remaining e.first e.second))
    (hd : MatchingDeck F lam P) (hnz : ∀ e, lam e ≠ 0) (e₀ : PortPair ι) :
    (∀ x, (F x / lam e₀).im = 0) ∧
    (∀ x, F (fun i => !(x i)) / lam e₀ = F x / lam e₀) ∧
    (∀ e, ∃ r : ℝ, 0 < r ∧ lam e / lam e₀ = (r : ℂ)) := by
  have hg : Tensor.ChargeLayer (fun x => F x / lam e₀) 0 := by
    intro x hx
    apply heo x
    intro hf
    exact hx (by simp [hf])
  have hp := normalized_deck_positive hn hd hnz e₀
  have hreal : ∀ a b (hab : a ≠ b) (y : Remaining a b → Bool),
      (loop a b hab (fun x => F x / lam e₀) y).im = 0 := by
    intro a b hab y
    obtain ⟨r, hr, he, hl⟩ := hp ⟨a,b,hab⟩
    have hh := congrFun hl y
    rw [hh]
    rcases literal_eq_zero_or_one (K := ℂ) (P ⟨a,b,hab⟩) y with hz | ho
    · simp [hz]
    · simp [ho]
  have hcomp : ∀ a b (hab : a ≠ b) (y : Remaining a b → Bool),
      loop a b hab (fun x => F x / lam e₀) (fun i => !(y i)) =
        loop a b hab (fun x => F x / lam e₀) y := by
    intro a b hab y
    obtain ⟨r, hr, he, hl⟩ := hp ⟨a,b,hab⟩
    rw [congrFun hl (fun i => !(y i)), congrFun hl y, literal_complement]
  obtain ⟨hR, hC⟩ := eo_real_complement_of_loops (by omega)
    (fun x => F x / lam e₀) hg hreal hcomp
  exact ⟨hR, hC, fun e => by obtain ⟨r, hr, he, hl⟩ := hp e; exact ⟨r, hr, he⟩⟩

/-- Coefficient field embeddings preserve the exact normalized matching deck. -/
theorem MatchingDeck.map [Semiring K] [Semiring L] (φ : K →+* L)
    {F : Tensor K ι} {lam : PortPair ι → K}
    {P : (e : PortPair ι) → XMatching (Remaining e.first e.second)}
    (hd : MatchingDeck F lam P) :
    MatchingDeck (fun x => φ (F x)) (fun e => φ (lam e)) P := by
  intro e
  funext y
  calc
    _ = φ (loop e.first e.second e.distinct F y) :=
      loop_map φ.toAddMonoidHom e.first e.second e.distinct F y
    _ = _ := by
      rw [hd]
      classical
      by_cases ht : Transversal (P e) y <;> simp [literal, ht]

/-- Source Lemma 8.6, with the normalizing scalar in the actual algebraic
complex field. The input itself is never asserted to be a realizable gadget. -/
theorem common_phase_algebraic [Fintype ι] (hn : 6 ≤ Fintype.card ι)
    (F : Tensor Tractable.AlgebraicComplex ι) (heo : Tensor.ChargeLayer F 0)
    (lam : PortPair ι → Tractable.AlgebraicComplex)
    (P : (e : PortPair ι) → XMatching (Remaining e.first e.second))
    (hd : MatchingDeck F lam P) (hnz : ∀ e, lam e ≠ 0) :
    ∃ c : Tractable.AlgebraicComplex, c ≠ 0 ∧
      (∀ x, ((F x / c : Tractable.AlgebraicComplex) : ℂ).im = 0) ∧
      (∀ x, F (fun i => !(x i)) / c = F x / c) ∧
      (∀ e, ∃ r : ℝ, 0 < r ∧ ((lam e / c : Tractable.AlgebraicComplex) : ℂ) = (r : ℂ)) ∧
      (∀ x, star (((F (fun i => !(x i)) / c : Tractable.AlgebraicComplex) : ℂ)) =
        ((F x / c : Tractable.AlgebraicComplex) : ℂ)) := by
  let φ : Tractable.AlgebraicComplex →+* ℂ := (algebraicClosure ℚ ℂ).val.toRingHom
  have hφ : Function.Injective φ := fun _ _ he => Subtype.ext he
  have hF : Tensor.ChargeLayer (fun x => φ (F x)) 0 := by
    intro x hx
    exact heo x (fun h => hx (by simp [h]))
  have hnz' : ∀ e, φ (lam e) ≠ 0 := by
    intro e hh
    apply hnz e
    apply hφ
    simpa using hh
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp (show 1 < Fintype.card ι by omega)
  let e₀ : PortPair ι := ⟨a,b,hab⟩
  obtain ⟨hR, hC, hP⟩ := common_phase_at hn (fun x => φ (F x)) hF
    (fun e => φ (lam e)) P (hd.map φ) hnz' e₀
  refine ⟨lam e₀, hnz e₀, ?_, ?_, ?_, ?_⟩
  · exact hR
  · intro x
    apply hφ
    simpa only [map_div₀] using hC x
  · exact hP
  · intro x
    change star (φ (F (fun i => !(x i))) / φ (lam e₀)) = φ (F x) / φ (lam e₀)
    rw [hC]
    exact Complex.conj_eq_iff_im.mpr (hR x)

/-- A displayed scalar of an algebraic input's literal deck is itself algebraic:
it is an actual contraction coefficient at a transversal word. -/
theorem algebraic_deck_scalar (F : Tensor Tractable.AlgebraicComplex ι)
    (lam : PortPair ι → ℂ)
    (P : (e : PortPair ι) → XMatching (Remaining e.first e.second))
    (hd : MatchingDeck (fun x => (F x : ℂ)) lam P) (e : PortPair ι) :
    ∃ a : Tractable.AlgebraicComplex, (a : ℂ) = lam e := by
  let y := word (P e) (fun _ => false)
  refine ⟨loop e.first e.second e.distinct F y, ?_⟩
  let φ : Tractable.AlgebraicComplex →+* ℂ := (algebraicClosure ℚ ℂ).val.toRingHom
  have hm := loop_map φ.toAddMonoidHom e.first e.second e.distinct F y
  have hv := congrFun (hd e) y
  have he : literal (P e) ℂ y = 1 := literal_word _ _
  rw [he, mul_one] at hv
  exact hm.symm.trans hv

/-- No algebraicity assumption on displayed complex deck scalars is necessary.
Their algebraicity follows from the actual contraction coefficients. -/
theorem common_phase_algebraic_input [Fintype ι] (hn : 6 ≤ Fintype.card ι)
    (F : Tensor Tractable.AlgebraicComplex ι) (heo : Tensor.ChargeLayer F 0)
    (lam : PortPair ι → ℂ)
    (P : (e : PortPair ι) → XMatching (Remaining e.first e.second))
    (hd : MatchingDeck (fun x => (F x : ℂ)) lam P) (hnz : ∀ e, lam e ≠ 0) :
    ∃ c : Tractable.AlgebraicComplex, c ≠ 0 ∧
      (∀ x, ((F x / c : Tractable.AlgebraicComplex) : ℂ).im = 0) ∧
      (∀ x, F (fun i => !(x i)) / c = F x / c) ∧
      (∀ e, ∃ r : ℝ, 0 < r ∧ lam e / (c : ℂ) = (r : ℂ)) ∧
      (∀ x, star (((F (fun i => !(x i)) / c : Tractable.AlgebraicComplex) : ℂ)) =
        ((F x / c : Tractable.AlgebraicComplex) : ℂ)) := by
  let φ : Tractable.AlgebraicComplex →+* ℂ := (algebraicClosure ℚ ℂ).val.toRingHom
  have hφ : Function.Injective φ := fun _ _ he => Subtype.ext he
  have hF : Tensor.ChargeLayer (fun x => (F x : ℂ)) 0 := by
    intro x hx
    exact heo x (fun h => hx (by simp [h]))
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp (show 1 < Fintype.card ι by omega)
  let e₀ : PortPair ι := ⟨a,b,hab⟩
  obtain ⟨c, hc⟩ := algebraic_deck_scalar F lam P hd e₀
  have hcnz : c ≠ 0 := by
    intro hz
    apply hnz e₀
    rw [← hc, hz]
    rfl
  obtain ⟨hR, hC, hP⟩ := common_phase_at hn (fun x => (F x : ℂ)) hF lam P hd hnz e₀
  refine ⟨c, hcnz, ?_, ?_, ?_, ?_⟩
  · intro x
    change ((F x : ℂ) / (c : ℂ)).im = 0
    rw [hc]
    exact hR x
  · intro x
    apply hφ
    change (F (fun i => !(x i)) : ℂ) / (c : ℂ) = (F x : ℂ) / (c : ℂ)
    rw [hc]
    exact hC x
  · rw [hc]
    exact hP
  · intro x
    change star ((F (fun i => !(x i)) : ℂ) / (c : ℂ)) = (F x : ℂ) / (c : ℂ)
    rw [hc, hC]
    exact Complex.conj_eq_iff_im.mpr (hR x)

end Paper2.CommonPhase
