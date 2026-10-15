import Paper2.Matching
import Paper2.EndpointSelfLoop
import Mathlib.Basic.Complex.Basic

/-!
# Literal X matching tensors on arbitrary finite port sets

The port equivalence retains every original occurrence. The zero-one table
below is the exact product of native-X factors, with no scalar normalization.
Every contraction is the actual two-state `EndpointSelfLoop.loop` operation.
-/

namespace Paper2.CommonPhase

variable {ι : Type} {K : Type*}

/-- An oriented perfect matching, without imposing a canonical port order. -/
structure XMatching (ι : Type) where
  count : ℕ
  ports : (Fin count × Bool) ≃ ι

/-- Every matched pair carries opposite bits. -/
def Transversal (P : XMatching ι) (x : ι → Bool) : Prop :=
  ∀ j, x (P.ports (j, true)) = !(x (P.ports (j, false)))

/-- The literal zero-one X matching tensor. -/
noncomputable def literal (P : XMatching ι) (K : Type*) [Zero K] [One K] :
    Tensor K ι := by
  classical
  exact fun x => if Transversal P x then 1 else 0

/-- Independent choices at the first endpoint of each matched pair. -/
def word (P : XMatching ι) (z : Fin P.count → Bool) : ι → Bool :=
  fun k => let jb := P.ports.symm k
    if jb.2 then !(z jb.1) else z jb.1

@[simp] theorem word_first (P : XMatching ι) (z : Fin P.count → Bool)
    (j : Fin P.count) : word P z (P.ports (j, false)) = z j := by
  simp [word]

@[simp] theorem word_second (P : XMatching ι) (z : Fin P.count → Bool)
    (j : Fin P.count) : word P z (P.ports (j, true)) = !(z j) := by
  simp [word]

@[simp] theorem transversal_word (P : XMatching ι) (z : Fin P.count → Bool) :
    Transversal P (word P z) := by
  simp [Transversal]

@[simp] theorem literal_word [Zero K] [One K] (P : XMatching ι)
    (z : Fin P.count → Bool) : literal P K (word P z) = 1 := by
  simp [literal]

theorem literal_eq_zero_or_one [Zero K] [One K] (P : XMatching ι)
    (x : ι → Bool) : literal P K x = 0 ∨ literal P K x = 1 := by
  classical
  by_cases h : Transversal P x <;> simp [literal, h]

theorem transversal_complement (P : XMatching ι) (x : ι → Bool) :
    Transversal P (fun i => !(x i)) ↔ Transversal P x := by
  constructor <;> intro h j <;> have hj := h j <;>
    cases ha : x (P.ports (j, false)) <;>
    cases hb : x (P.ports (j, true)) <;> simp_all

/-- Literal X products are invariant under simultaneous bit complement. -/
theorem literal_complement [Zero K] [One K] (P : XMatching ι)
    (x : ι → Bool) : literal P K (fun i => !(x i)) = literal P K x := by
  classical
  simp only [literal, transversal_complement]

/-- Any two distinct ports can be made opposite while preserving all matching
constraints, including when the ports belong to different matched pairs. -/
theorem exists_literal_opposite [Zero K] [One K] (P : XMatching ι)
    (a b : ι) (hab : a ≠ b) :
    ∃ x : ι → Bool, literal P K x = 1 ∧ x b = !(x a) := by
  classical
  obtain ⟨⟨i, s⟩, rfl⟩ := P.ports.surjective a
  obtain ⟨⟨j, t⟩, rfl⟩ := P.ports.surjective b
  by_cases hij : i = j
  · subst j
    refine ⟨word P (fun _ => false), literal_word _ _, ?_⟩
    cases s <;> cases t <;> simp_all
  · refine ⟨word P (fun k => if k = i then s else !t), literal_word _ _, ?_⟩
    cases s <;> cases t <;> simp [word, Ne.symm hij]

/-- Each actual two-state contraction coefficient is zero, one, or two. -/
theorem loop_literal_eq_zero_or_one_or_two [Semiring K] (P : XMatching ι)
    (a b : ι) (hab : a ≠ b) (y : EndpointSelfLoop.Remaining a b → Bool) :
    EndpointSelfLoop.loop a b hab (literal P K) y = 0 ∨
      EndpointSelfLoop.loop a b hab (literal P K) y = 1 ∨
      EndpointSelfLoop.loop a b hab (literal P K) y = 2 := by
  change (∑ t : Bool, literal P K (EndpointSelfLoop.extendPair a b hab y t)) = 0 ∨
    (∑ t : Bool, literal P K (EndpointSelfLoop.extendPair a b hab y t)) = 1 ∨
    (∑ t : Bool, literal P K (EndpointSelfLoop.extendPair a b hab y t)) = 2
  rw [Fintype.sum_bool]
  rcases literal_eq_zero_or_one (K := K) P
      (EndpointSelfLoop.extendPair a b hab y false) with h₀ | h₀ <;>
    rcases literal_eq_zero_or_one (K := K) P
      (EndpointSelfLoop.extendPair a b hab y true) with h₁ | h₁ <;>
    simp [h₀, h₁, one_add_one_eq_two]

/-- For every port pair, at least one actual residual coefficient is one or
two. In particular this assertion does not substitute a normalized matching. -/
theorem exists_loop_literal_eq_one_or_two [Semiring K] (P : XMatching ι)
    (a b : ι) (hab : a ≠ b) :
    ∃ y : EndpointSelfLoop.Remaining a b → Bool,
      EndpointSelfLoop.loop a b hab (literal P K) y = 1 ∨
      EndpointSelfLoop.loop a b hab (literal P K) y = 2 := by
  classical
  obtain ⟨x, hx, hxab⟩ := exists_literal_opposite (K := K) P a b hab
  refine ⟨EndpointSelfLoop.restrict a b x, ?_⟩
  rw [EndpointSelfLoop.loop_apply_restrict a b hab _ x hxab, hx]
  rcases literal_eq_zero_or_one (K := K) P
      (fun i => x (Equiv.swap a b i)) with h | h <;>
    simp [h, one_add_one_eq_two]

/-- Over the complex numbers, every pair contraction of a literal X matching
is genuinely nonzero. -/
theorem exists_loop_literal_ne_zero (P : XMatching ι)
    (a b : ι) (hab : a ≠ b) :
    ∃ y : EndpointSelfLoop.Remaining a b → Bool,
      EndpointSelfLoop.loop a b hab (literal P ℂ) y ≠ 0 := by
  obtain ⟨y, h | h⟩ := exists_loop_literal_eq_one_or_two (K := ℂ) P a b hab
  · exact ⟨y, by rw [h]; norm_num⟩
  · exact ⟨y, by rw [h]; norm_num⟩

/-- Retain the exact port occurrence bijection of the original matching API. -/
def ofPairing {n : ℕ} (p : Matching.Pairing n) : XMatching (Fin n) where
  count := p.count
  ports := p.ports

@[simp] theorem word_ofPairing {n : ℕ} (p : Matching.Pairing n)
    (z : Fin p.count → Bool) :
    word (ofPairing p) z = Matching.word p (fun _ => true) z := by
  funext k
  simp [word, ofPairing, Matching.word]
  rfl

/-- Every binary factor is exactly the corresponding zero-one constraint. -/
theorem bell_x_eq_indicator [CommRing K] (a b : Bool) :
    Bell.ordered (K := K) true false a b = if b = !a then 1 else 0 := by
  cases a <;> cases b <;> rfl

/-- On arbitrary port sets, the literal is exactly the tensor product of X
factors along the matching's retained port bijection. -/
theorem literal_eq_prod [CommRing K] (P : XMatching ι) (x : ι → Bool) :
    literal P K x =
      ∏ j, Bell.ordered (K := K) true false
        (x (P.ports (j, false))) (x (P.ports (j, true))) := by
  classical
  simp only [bell_x_eq_indicator]
  by_cases h : Transversal P x
  · rw [literal, ite_eq_left h]
    symm
    apply Finset.prod_eq_one
    intro j hj
    exact ite_eq_left (h j)
  · rw [literal, ite_eq_right h]
    symm
    simp only [Transversal] at h
    push Not at h
    obtain ⟨j, hj⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

/-- The generic-port literal is exactly the original unscaled X factor product. -/
theorem literal_ofPairing [CommRing K] {n : ℕ} (p : Matching.Pairing n)
    (x : Fin n → Bool) :
    literal (ofPairing p) K x =
      ∏ j, Bell.ordered (K := K) true false
        (x (p.ports (j, false))) (x (p.ports (j, true))) :=
  literal_eq_prod (ofPairing p) x

/-- Faithful bridge to `Matching.bellProduct`, preserving the overall scalar. -/
theorem bellProduct_eq_mul_literal [CommRing K] {n : ℕ}
    (p : Matching.Pairing n) (c : K) :
    Matching.bellProduct p (fun _ => true) (fun _ => false) c =
      fun x => c * literal (ofPairing p) K x := by
  funext x
  rw [literal_ofPairing]
  rfl

end Paper2.CommonPhase
