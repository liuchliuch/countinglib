import Paper2.ExactInput.FixedRootCodec.VariableRootBisectionInit

/-! Quantitative correctness of the automatically initialized variable root
refinement. The Cauchy bound is derived from actual coefficient bytes. Every
genuine distinct root receives an active slot whose rational approximation has
the requested error; no numeric-height or root-location premise is supplied. -/
namespace Paper2.ExactInput.FixedRootCodec.VariableRootBisection
open Computability Paper2.Algebraic Paper2.Complexity Polynomial
open BinaryCompose FixedFieldMachines BellMachines GraphPreprocessing
open Holant.LocalDrafts.EffectiveAlgebraic
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n d : ℕ}

theorem radius_positive (v : Fin n → ℚ) : 0 < radius v := by unfold radius; positivity

theorem real_root_bound (v : Fin n → ℚ) (hp : VariablePolynomial.polynomial v ≠ 0)
    (r : ℝ) (hr : (VariablePolynomial.polynomial v).aeval r = 0) :
    |r| < (radius v : ℝ) := by
  let p := VariablePolynomial.polynomial v
  have hc : p.aeval (r : ℂ) = 0 := by
    change p.aeval (IsScalarTower.toAlgHom ℚ ℝ ℂ r) = 0
    rw [Polynomial.aeval_algHom_apply,hr,map_zero]
  have hroot : (p.map (Rat.castHom ℂ)).IsRoot (r : ℂ) := by
    rw [Polynomial.IsRoot,Polynomial.eval_map]
    exact hc
  have hn := (hroot.norm_lt_cauchyBound (Polynomial.map_ne_zero hp)).trans_le
    (Paper2.ExactInput.rational_cauchyBound_le (coefficient_height_bound v))
  have hn' : ‖(r : ℂ)‖ < (2 : ℝ)^(2*coefficientHeight v+1) := by exact_mod_cast hn
  have hreal : |r| < (2 : ℝ)^(2*coefficientHeight v+1) := by
    simpa only [Complex.norm_real,Real.norm_eq_abs] using hn'
  have he : 2*coefficientHeight v+1 ≤ radiusExponent v := by
    simp [coefficientHeight,radiusExponent]
    omega
  apply hreal.trans_le
  unfold radius
  norm_cast
  exact pow_le_pow_right₀ (by norm_num) he

theorem initial_lower (v : Fin n → ℚ) :
    (stateInterval (initialBracket v)).lower = -(radius v : ℚ) := by
  simp [initialBracket,stateInterval,Rat.mkRat_eq_divInt,Rat.divInt_eq_div]

theorem initial_upper (v : Fin n → ℚ) :
    (stateInterval (initialBracket v)).upper = (radius v : ℚ) := by
  simp [initialBracket,stateInterval,Rat.mkRat_eq_divInt,Rat.divInt_eq_div]

theorem initial_contains (v : Fin n → ℚ) (hp : VariablePolynomial.polynomial v ≠ 0)
    (r : ℝ) (hr : (VariablePolynomial.polynomial v).aeval r = 0) :
    ClosedContains (initialState v) r := by
  have hb := abs_lt.mp (real_root_bound v hp r hr)
  unfold ClosedContains
  simp only [initialState,initial_lower,initial_upper,Rat.cast_neg,Rat.cast_natCast]
  exact ⟨hb.1.le,hb.2.le⟩

theorem initial_width (v : Fin n → ℚ) :
    (stateInterval (initialBracket v)).width = 2*(radius v : ℚ) := by
  rw [RealIsolation.Interval.width,initial_upper,initial_lower]
  ring

theorem initial_epsilon (v : Fin n → ℚ) : epsilon (initialBracket v) = 1 := by
  simp [epsilon,initialBracket,Rat.mkRat_eq_divInt,Rat.divInt_eq_div]

theorem rounds_eq (t : ℕ) (v : Fin n → ℚ) :
    rounds t v = 4*t+2*((vectorEncoding n).encode v).length+10 := by
  simp only [rounds,requestEncoding,pairEncoding_length,UnaryBinary.unaryEncoding,
    List.length_replicate]
  omega

theorem initial_refined_width_bound (t : ℕ) (v : Fin n → ℚ) :
    ((stateInterval (initialBracket v)).width+2*epsilon (initialBracket v)) /
      (2 : ℚ)^(rounds t v) ≤ 1/(2 : ℚ)^t := by
  rw [initial_width,initial_epsilon]
  have hr : (1 : ℚ) ≤ (radius v : ℚ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (radius_positive v).ne'
  have hwidth : 2*(radius v : ℚ)+2*1 ≤ (2 : ℚ)^(radiusExponent v+2) := by
    have he : (2 : ℚ)^(radiusExponent v+2) = 4*(radius v : ℚ) := by
      simp [radius,pow_add]
      ring
    rw [he]
    linarith
  apply (div_le_div_of_nonneg_right hwidth (by positivity)).trans
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  simp only [one_mul]
  rw [← pow_add]
  apply pow_le_pow_right₀ (by norm_num)
  rw [rounds_eq]
  simp only [radiusExponent]
  omega

theorem approximate_error (count : CountFunction n) (j t : ℕ) (v : Fin n → ℚ)
    (hp : VariablePolynomial.polynomial v ≠ 0) (r : ℝ)
    (hr : (VariablePolynomial.polynomial v).aeval r = 0)
    (hcount : ∀ q : ℚ, count v q ≤ j ↔ (q : ℝ) < r) :
    |(approximate count j t v : ℝ)-r| < 1/(2 : ℝ)^t := by
  have he := point_error count j (rounds t v) (initialState v) r
    (by simp [initialState,initialBracket]) (initial_contains v hp r hr) hcount
  have hw := (Rat.cast_le (K := ℝ)).mpr (initial_refined_width_bound t v)
  dsimp only [initialState] at he
  push_cast at hw he
  exact he.trans_le hw

theorem sorted_count_at_radius (v : Fin n → ℚ) (hp : VariablePolynomial.polynomial v ≠ 0)
    (roots : Fin d → ℝ) (hr : ∀ i, (VariablePolynomial.polynomial v).aeval (roots i) = 0) :
    sortedPrefixCount roots (radius v : ℚ) = d := by
  classical
  have he : Finset.univ.filter (fun i => roots i ≤ ((radius v : ℚ) : ℝ)) =
      (Finset.univ : Finset (Fin d)) := by
    apply Finset.filter_eq_self.mpr
    intro i _
    have h := (abs_le.mp (real_root_bound v hp (roots i) (hr i)).le).2
    simpa using h
  rw [sortedPrefixCount,he,Finset.card_univ,Fintype.card_fin]

theorem active_iff_rank (count : CountFunction n) (v : Fin n → ℚ)
    (hp : VariablePolynomial.polynomial v ≠ 0) (roots : Fin d → ℝ)
    (hr : ∀ i, (VariablePolynomial.polynomial v).aeval (roots i) = 0)
    (hcount : ∀ q : ℚ, count v q = sortedPrefixCount roots q) (j : ℕ) :
    active count j v = true ↔ j < d := by
  rw [active,hcount,sorted_count_at_radius v hp roots hr]
  simp

theorem sorted_root_approximate_error (count : CountFunction n) (v : Fin n → ℚ)
    (hp : VariablePolynomial.polynomial v ≠ 0) (roots : Fin d → ℝ)
    (hroots : StrictMono roots)
    (hr : ∀ i, (VariablePolynomial.polynomial v).aeval (roots i) = 0)
    (hcount : ∀ q : ℚ, count v q = sortedPrefixCount roots q) (j : Fin d) (t : ℕ) :
    |(approximate count j.val t v : ℝ)-roots j| < 1/(2 : ℝ)^t :=
  approximate_error count j.val t v hp (roots j) (hr j)
    (fun q => by rw [hcount q]; exact sortedPrefixCount_le_iff roots hroots j q)

/-- A dense vector of n entries has degree less than n whenever its polynomial
is nonzero; arbitrary zero padding is permitted. -/
theorem polynomial_degree_lt (v : Fin n → ℚ) (hp : VariablePolynomial.polynomial v ≠ 0) :
    (VariablePolynomial.polynomial v).natDegree < n := by
  rw [Polynomial.natDegree_lt_iff_degree_lt hp,Polynomial.degree_lt_iff_coeff_zero]
  intro j hj
  rw [VariablePolynomial.coefficient_eq,dif_neg (by omega)]

theorem sorted_root_slots_bound (v : Fin n → ℚ) (hp : VariablePolynomial.polynomial v ≠ 0)
    (roots : Fin d → ℝ) (hroots : StrictMono roots)
    (hr : ∀ i, (VariablePolynomial.polynomial v).aeval (roots i) = 0) : d ≤ n := by
  classical
  let p := (VariablePolynomial.polynomial v).map (algebraMap ℚ ℝ)
  let S := Finset.univ.image roots
  have hs : S.card = d := by
    dsimp [S]
    rw [Finset.card_image_of_injective _ hroots.injective,Finset.card_univ,Fintype.card_fin]
  have hmem : S.val ⊆ p.roots := by
    intro r hmem
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp (show r ∈ S from hmem)
    apply (Polynomial.mem_roots (Polynomial.map_ne_zero hp)).mpr
    rw [Polynomial.IsRoot,Polynomial.eval_map]
    exact hr i
  have hb := Polynomial.card_le_degree_of_subset_roots hmem
  rw [hs] at hb
  have he : p.natDegree = (VariablePolynomial.polynomial v).natDegree :=
    Polynomial.natDegree_map_eq_of_injective (algebraMap ℚ ℝ).injective _
  exact hb.trans (he.le.trans (polynomial_degree_lt v hp).le)

/-- Every genuine sorted root occurs in the actual fixed-capacity list with
an active flag and the requested approximation accuracy. -/
theorem approximations_cover (count : CountFunction n) (v : Fin n → ℚ)
    (hp : VariablePolynomial.polynomial v ≠ 0) (roots : Fin d → ℝ)
    (hroots : StrictMono roots)
    (hr : ∀ i, (VariablePolynomial.polynomial v).aeval (roots i) = 0)
    (hcount : ∀ q : ℚ, count v q = sortedPrefixCount roots q) (t : ℕ) (j : Fin d) :
    ∃ q : ℚ, (true,q) ∈ approximations count t v ∧
      |(q : ℝ)-roots j| < 1/(2 : ℝ)^t := by
  let index : Fin n := ⟨j.val,lt_of_lt_of_le j.isLt (sorted_root_slots_bound v hp roots hroots hr)⟩
  refine ⟨approximate count j.val t v,?_,sorted_root_approximate_error count v hp roots
    hroots hr hcount j t⟩
  have ha := (active_iff_rank count v hp roots hr hcount j.val).mpr j.isLt
  apply List.mem_map.mpr
  refine ⟨index,List.mem_finRange _,?_⟩
  simp only [slot,index,ha]

end
end Paper2.ExactInput.FixedRootCodec.VariableRootBisection
