import Paper2.CommonPhase.Phase
import Paper2.WeightedMatching

/-! Actual weighted matching tensors and their native-X sums on named ports. -/
namespace Paper2.MatchingPropagation
open CommonPhase EndpointSelfLoop
variable {ι : Type} {K : Type*}

abbrev Matching := XMatching

/-- The actual tensor product of nonsingular anti-diagonal binary factors. -/
def product [CommRing K] (P : Matching ι) (p q : Fin P.count → K) (c : K) :
    Tensor K ι := fun x => c * ∏ j,
      WeightedMatching.binary (p j) (q j) (x (P.ports (j, false))) (x (P.ports (j, true)))

/-- Zero is excluded, as in the source's binary-product class. -/
def IsWeighted [CommRing K] (F : Tensor K ι) : Prop :=
  ∃ (P : Matching ι) (p q : Fin P.count → K) (c : K),
    c ≠ 0 ∧ (∀ j, p j ≠ 0) ∧ (∀ j, q j ≠ 0) ∧ F = product P p q c

/-- Source ARS factors, with a nonzero overall scalar. -/
def IsARS (F : Tensor ℂ ι) : Prop :=
  ∃ (P : Matching ι) (a : Fin P.count → ℂ) (c : ℂ),
    c ≠ 0 ∧ (∀ j, a j ≠ 0) ∧ F = product P a (fun j => star (a j)) c

/-- A nonzero scalar multiple of the literal matching table. -/
def IsX [CommRing K] (F : Tensor K ι) : Prop :=
  ∃ (P : Matching ι) (c : K), c ≠ 0 ∧ F = fun x => c * literal P K x

/-- The mate retains the original named port, independently of orientation. -/
def mate (P : Matching ι) (a : ι) : ι :=
  P.ports ((P.ports.symm a).1, !(P.ports.symm a).2)

@[simp] theorem mate_port (P : Matching ι) (j : Fin P.count) (b : Bool) :
    mate P (P.ports (j,b)) = P.ports (j,!b) := by simp [mate]

@[simp] theorem mate_mate (P : Matching ι) (a : ι) : mate P (mate P a) = a := by
  simp [mate]

@[simp] theorem mate_ne (P : Matching ι) (a : ι) : mate P a ≠ a := by
  obtain ⟨⟨j,b⟩, rfl⟩ := P.ports.surjective a
  simp only [mate_port, ne_eq, Equiv.apply_eq_iff_eq, Prod.mk.injEq, true_and]
  cases b <;> decide

theorem transversal_iff_mate (P : Matching ι) (x : ι → Bool) :
    Transversal P x ↔ ∀ a, x (mate P a) = !(x a) := by
  constructor
  · intro h a
    obtain ⟨⟨j,b⟩, rfl⟩ := P.ports.surjective a
    cases b
    · simpa using h j
    · simpa using congrArg Bool.not (h j).symm
  · intro h j
    simpa using h (P.ports (j,false))

theorem product_ne_zero [CommRing K] [IsDomain K] (P : Matching ι)
    (p q : Fin P.count → K) (c : K) (hc : c ≠ 0)
    (hp : ∀ j, p j ≠ 0) (hq : ∀ j, q j ≠ 0) (x : ι → Bool) :
    product P p q c x ≠ 0 ↔ Transversal P x := by
  simp [product, hc, Finset.prod_ne_zero_iff,
    WeightedMatching.binary_ne_zero (hp _) (hq _), Transversal]

theorem IsARS.weighted {F : Tensor ℂ ι} (h : IsARS F) : IsWeighted F := by
  obtain ⟨P,a,c,hc,ha,rfl⟩ := h
  exact ⟨P,a,fun j => star (a j),c,hc,ha,fun j => by simpa using ha j,rfl⟩

theorem product_eq_literal [CommRing K] (P : Matching ι)
    (p : Fin P.count → K) (c : K) :
    product P p p c = fun x => (c * ∏ j, p j) * literal P K x := by
  classical
  funext x
  rw [literal_eq_prod]
  simp only [product, mul_assoc]
  congr 1
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  cases x (P.ports (j,false)) <;> cases x (P.ports (j,true)) <;>
    simp [WeightedMatching.binary, bell_x_eq_indicator]

theorem weighted_isX_of_equal [CommRing K] [IsDomain K] (P : Matching ι)
    (p q : Fin P.count → K) (c : K) (hc : c ≠ 0) (hp : ∀ j, p j ≠ 0)
    (he : ∀ j, p j = q j) : IsX (product P p q c) := by
  have h : p = q := funext he
  subst q
  exact ⟨P,c * ∏ j, p j,mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr (fun j _ => hp j)),
    product_eq_literal P p c⟩

/-- Having exactly one nonzero value; this property retains its actual scalar. -/
def Flat [Zero K] (F : Tensor K ι) : Prop :=
  ∀ x y, F x ≠ 0 → F y ≠ 0 → F x = F y

theorem isX_flat [CommRing K] {F : Tensor K ι} (h : IsX F) : Flat F := by
  obtain ⟨P,c,hc,rfl⟩ := h
  intro x y hx hy
  change c * literal P K x = c * literal P K y
  rcases literal_eq_zero_or_one (K := K) P x with h | h
  · simp [h] at hx
  · rcases literal_eq_zero_or_one (K := K) P y with h' | h'
    · simp [h'] at hy
    · rw [h,h']

@[simp] theorem fill_first (e : PortPair ι) (x : ι → Bool) (t : Bool) :
    e.fill x t e.first = t := by
  classical
  simp [PortPair.fill]

@[simp] theorem fill_second (e : PortPair ι) (x : ι → Bool) (t : Bool) :
    e.fill x t e.second = !t := by
  classical
  simp [PortPair.fill, e.distinct.symm]

theorem fill_other (e : PortPair ι) (x : ι → Bool) (t : Bool) (a : ι)
    (ha : a ≠ e.first) (hb : a ≠ e.second) : e.fill x t a = x a := by
  classical
  simp [PortPair.fill,ha,hb]

/-- If both inserted states satisfy the matching, the deleted ports are mates. -/
theorem two_fills_transversal (P : Matching ι) (e : PortPair ι) (x : ι → Bool)
    (h₀ : Transversal P (e.fill x false)) (h₁ : Transversal P (e.fill x true)) :
    mate P e.first = e.second := by
  by_contra h
  have h₀' := (transversal_iff_mate P _).mp h₀ e.first
  have h₁' := (transversal_iff_mate P _).mp h₁ e.first
  rw [fill_other e x false _ (mate_ne P _) h, fill_first] at h₀'
  rw [fill_other e x true _ (mate_ne P _) h, fill_first] at h₁'
  simp_all

/-- Removing a matching edge admits either both native-X states or neither. -/
theorem fills_transversal_iff_of_mate (P : Matching ι) (e : PortPair ι)
    (he : mate P e.first = e.second) (x : ι → Bool) (s t : Bool) :
    Transversal P (e.fill x s) ↔ Transversal P (e.fill x t) := by
  have he' : mate P e.second = e.first := by rw [← he, mate_mate]
  suffices hh : ∀ s t, Transversal P (e.fill x s) → Transversal P (e.fill x t) from
    ⟨hh s t, hh t s⟩
  intro s t h
  rw [transversal_iff_mate] at h ⊢
  intro a
  by_cases ha : a = e.first
  · subst a; simp [he]
  · by_cases hb : a = e.second
    · subst a; simp [he']
    · have hma : mate P a ≠ e.first := by
        intro hma
        have := congrArg (mate P) hma
        exact hb (by simpa [he] using this)
      have hmb : mate P a ≠ e.second := by
        intro hmb
        have := congrArg (mate P) hmb
        exact ha (by simpa [he'] using this)
      simpa only [fill_other e x _ a ha hb, fill_other e x _ _ hma hmb] using h a

/-- The literal's native-X sum is constant on its support: scalar two for a
removed edge, scalar one for two spliced edges. No closure axiom is used. -/
theorem pairSum_literal_flat (P : Matching ι) (e : PortPair ι) :
    Flat (e.pairSum (literal P ℂ)) := by
  classical
  by_cases he : mate P e.first = e.second
  · have hv : ∀ x, e.pairSum (literal P ℂ) x =
        if Transversal P (e.fill x false) then 2 else 0 := by
      intro x
      have hh := fills_transversal_iff_of_mate P e he x true false
      simp only [PortPair.pairSum, Fintype.sum_bool]
      by_cases hx : Transversal P (e.fill x false) <;>
        simp [literal,hh,hx,one_add_one_eq_two]
    intro x y hx hy
    rw [hv] at hx hy ⊢
    rw [hv]
    split_ifs at hx hy ⊢ <;> simp_all
  · have hv : ∀ x, e.pairSum (literal P ℂ) x = 0 ∨
        e.pairSum (literal P ℂ) x = 1 := by
      intro x
      have hh : ¬ (Transversal P (e.fill x false) ∧ Transversal P (e.fill x true)) :=
        fun h => he (two_fills_transversal P e x h.1 h.2)
      simp only [PortPair.pairSum, Fintype.sum_bool]
      by_cases h₀ : Transversal P (e.fill x false) <;>
        by_cases h₁ : Transversal P (e.fill x true) <;>
        simp_all [literal]
    intro x y hx hy
    rcases hv x with h | h
    · exact False.elim (hx h)
    · rcases hv y with h' | h'
      · exact False.elim (hy h')
      · exact h.trans h'.symm

theorem pairSum_isX_flat (e : PortPair ι) {F : Tensor ℂ ι} (h : IsX F) :
    Flat (e.pairSum F) := by
  obtain ⟨P,c,hc,rfl⟩ := h
  rw [PortPair.pairSum_mul]
  intro x y hx hy
  exact congrArg (c * ·) (pairSum_literal_flat P e x y
    (fun hz => hx (by simp [hz])) (fun hz => hy (by simp [hz])))

end Paper2.MatchingPropagation
