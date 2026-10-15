import Paper2.Matching
import Mathlib.Tactic.Ring

/-! The exact weighted matching class of §7.1: nonzero products of oriented
anti-diagonal binary factors. Neither arbitrary invertible binary factors nor
only the unweighted X factors are substituted for the source definition. -/
namespace Paper2.WeightedMatching

abbrev Pairing := Tractable.OrientedPerfectPairing

variable {K : Type*} [CommRing K] [IsDomain K]

/-- The ordered matrix `[[0,p],[q,0]]`. -/
def binary (p q : K) (a b : Bool) : K :=
  if a then (if b then 0 else q) else (if b then p else 0)

/-- Literal tensor product, including its nonzero overall scalar. -/
def product {n : ℕ} (P : Pairing n) (p q : Fin P.count → K)
    (c : K) : Signature K n := fun x =>
  c * ∏ j, binary (p j) (q j) (x (P.ports (j, false))) (x (P.ports (j, true)))

/-- Source-exact membership of `B_×`; the zero signature is excluded. -/
def IsProduct {n : ℕ} (f : Signature K n) : Prop :=
  ∃ (P : Pairing n) (p q : Fin P.count → K) (c : K),
    c * ∏ j, p j * q j ≠ 0 ∧ f = product P p q c

abbrev word {n : ℕ} (P : Pairing n) := Matching.word P (fun _ => true)

@[simp] theorem word_first {n : ℕ} (P : Pairing n) (z : Fin P.count → Bool)
    (j : Fin P.count) : word P z (P.ports (j, false)) = z j := by
  simp [word]

@[simp] theorem word_second {n : ℕ} (P : Pairing n) (z : Fin P.count → Bool)
    (j : Fin P.count) : word P z (P.ports (j, true)) = !(z j) := by
  simp [word]

/-- Full transversal support of a perfect matching. -/
def Transversal {n : ℕ} (P : Pairing n) (x : Fin n → Bool) : Prop :=
  ∀ j, x (P.ports (j, true)) = !(x (P.ports (j, false)))

theorem transversal_iff_word {n : ℕ} (P : Pairing n) (x : Fin n → Bool) :
    Transversal P x ↔ ∃ z, word P z = x := by
  rw [← Matching.pair_constraints_iff_word]
  unfold Transversal
  constructor <;> intro h j <;> have hj := h j <;>
    cases ha : x (P.ports (j, false)) <;>
    cases hb : x (P.ports (j, true)) <;> simp_all

@[simp] theorem transversal_word {n : ℕ} (P : Pairing n) (z : Fin P.count → Bool) :
    Transversal P (word P z) := by
  simp [Transversal]

theorem parameters_nonzero {n : ℕ} (P : Pairing n) (p q : Fin P.count → K)
    (c : K) (h : c * ∏ j, p j * q j ≠ 0) :
    c ≠ 0 ∧ (∀ j, p j ≠ 0) ∧ (∀ j, q j ≠ 0) := by
  simpa [Finset.prod_ne_zero_iff, forall_and] using h

theorem binary_ne_zero {p q : K} (hp : p ≠ 0) (hq : q ≠ 0) (a b : Bool) :
    binary p q a b ≠ 0 ↔ b = !a := by
  cases a <;> cases b <;> simp [binary, hp, hq]

theorem product_ne_zero {n : ℕ} (P : Pairing n) (p q : Fin P.count → K)
    (c : K) (h : c * ∏ j, p j * q j ≠ 0) (x : Fin n → Bool) :
    product P p q c x ≠ 0 ↔ Transversal P x := by
  obtain ⟨hc, hp, hq⟩ := parameters_nonzero P p q c h
  simp [product, hc, Finset.prod_ne_zero_iff, binary_ne_zero (hp _) (hq _), Transversal]

theorem support_product {n : ℕ} (P : Pairing n) (p q : Fin P.count → K)
    (c : K) (h : c * ∏ j, p j * q j ≠ 0) :
    Matching.support (product P p q c) = Finset.univ.image (word P) := by
  classical
  ext x
  simp only [Matching.support, Finset.mem_filter, Finset.mem_univ, true_and,
    product_ne_zero P p q c h, transversal_iff_word, Finset.mem_image]

theorem card_support_product {n : ℕ} (P : Pairing n) (p q : Fin P.count → K)
    (c : K) (h : c * ∏ j, p j * q j ≠ 0) :
    (Matching.support (product P p q c)).card = 2 ^ P.count := by
  classical
  rw [support_product P p q c h,
    Finset.card_image_of_injective _ (Matching.word_injective P (fun _ => true))]
  simp

/-- A support word is uniquely specified by the first endpoint of each pair. -/
noncomputable def supportEquiv {n : ℕ} (P : Pairing n) (p q : Fin P.count → K)
    (c : K) (h : c * ∏ j, p j * q j ≠ 0) :
    (Fin P.count → Bool) ≃ {x // product P p q c x ≠ 0} where
  toFun z := ⟨word P z, (product_ne_zero P p q c h _).2 (transversal_word P z)⟩
  invFun x j := x.val (P.ports (j, false))
  left_inv z := by ext j; simp
  right_inv x := by
    apply Subtype.ext
    obtain ⟨z, hz⟩ := (transversal_iff_word P x.val).1
      ((product_ne_zero P p q c h x.val).1 x.property)
    change word P (fun j => x.val (P.ports (j, false))) = x.val
    rw [← hz]
    simp

/-- The unoriented pair relation retained by a matching. -/
def Paired {n : ℕ} (P : Pairing n) (u v : Fin n) : Prop :=
  (P.ports.symm u).1 = (P.ports.symm v).1 ∧
    (P.ports.symm u).2 ≠ (P.ports.symm v).2

/-- Two ports are forced opposite on every transversal exactly when paired.
The reverse implication varies a single independent pair choice. -/
theorem paired_iff_forall_word {n : ℕ} (P : Pairing n) (u v : Fin n) :
    Paired P u v ↔ ∀ z, word P z v = !(word P z u) := by
  obtain ⟨⟨i, a⟩, rfl⟩ := P.ports.surjective u
  obtain ⟨⟨j, b⟩, rfl⟩ := P.ports.surjective v
  simp only [Paired, Equiv.symm_apply_apply]
  constructor
  · rintro ⟨rfl, hab⟩ z
    cases a <;> cases b <;> simp_all
  · intro h
    have hij : i = j := by
      by_contra hij
      have hz := h (fun k => if k = i then a else b)
      cases a <;> cases b <;> simp [word, Matching.word, Ne.symm hij] at hz
    subst j
    refine ⟨rfl, ?_⟩
    intro hab
    subst b
    have hz := h (fun _ => false)
    cases a <;> simp at hz

/-- Full support determines every unoriented port pair, allowing all factor
permutations and all orientation reversals. -/
theorem same_transversals_same_pairs {n : ℕ} (P Q : Pairing n)
    (h : ∀ x, Transversal P x ↔ Transversal Q x) (u v : Fin n) :
    Paired P u v ↔ Paired Q u v := by
  rw [paired_iff_forall_word, paired_iff_forall_word]
  constructor <;> intro huv z
  · obtain ⟨w, hw⟩ := (transversal_iff_word P (word Q z)).1
      ((h _).2 (transversal_word Q z))
    rw [← hw]
    exact huv w
  · obtain ⟨w, hw⟩ := (transversal_iff_word Q (word P z)).1
      ((h _).1 (transversal_word P z))
    rw [← hw]
    exact huv w

/-- Equality of weighted-product supports determines the underlying pairs. -/
theorem same_product_support_same_pairs {n : ℕ} (P Q : Pairing n)
    (p q : Fin P.count → K) (a b : Fin Q.count → K) (c d : K)
    (hP : c * ∏ j, p j * q j ≠ 0) (hQ : d * ∏ j, a j * b j ≠ 0)
    (h : ∀ x, product P p q c x ≠ 0 ↔ product Q a b d x ≠ 0)
    (u v : Fin n) : Paired P u v ↔ Paired Q u v := by
  apply same_transversals_same_pairs P Q _ u v
  intro x
  simpa only [product_ne_zero P p q c hP, product_ne_zero Q a b d hQ] using h x

/-- Pulling a matching product back along another full-support matching
retains a product of unary coefficients in its independent pair choices. -/
def UnaryProduct {d : ℕ} (f : (Fin d → Bool) → K) : Prop :=
  ∃ (c : K) (u : Fin d → Bool → K), ∀ z, f z = c * ∏ j, u j (z j)

def orient (side bit : Bool) : Bool := if side then !bit else bit

@[simp] theorem word_apply {n : ℕ} (P : Pairing n) (z : Fin P.count → Bool)
    (k : Fin n) : word P z k = orient (P.ports.symm k).2 (z (P.ports.symm k).1) := by
  simp [word, Matching.word, orient]

theorem product_unary_of_same_support {n : ℕ} (P Q : Pairing n)
    (h : ∀ x, Transversal P x ↔ Transversal Q x)
    (p q : Fin Q.count → K) (c : K) :
    UnaryProduct (fun z => product Q p q c (word P z)) := by
  classical
  let r : Fin Q.count → Fin P.count := fun k => (P.ports.symm (Q.ports (k, false))).1
  let w : Fin Q.count → Bool → K := fun k b =>
    binary (p k) (q k) (orient (P.ports.symm (Q.ports (k, false))).2 b)
      (orient (P.ports.symm (Q.ports (k, true))).2 b)
  refine ⟨c, fun j b => ∏ k, if r k = j then w k b else 1, ?_⟩
  intro z
  have hp : ∀ k, (P.ports.symm (Q.ports (k, true))).1 = r k := by
    intro k
    have hq : Paired Q (Q.ports (k, false)) (Q.ports (k, true)) := by simp [Paired]
    exact ((same_transversals_same_pairs P Q h _ _).2 hq).1.symm
  change c * (∏ j, binary (p j) (q j) (word P z (Q.ports (j, false)))
      (word P z (Q.ports (j, true)))) = c * _
  apply congrArg (fun t : K => c * t)
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro k hk
  simp [word_apply, hp, r, w]

/-- Any two-dimensional slice of a three-unary product has zero determinant.
Here the first bit is fixed to false and the final two bits vary. -/
theorem unary_product_minor {f : (Fin 3 → Bool) → K} (h : UnaryProduct f) :
    f ![false, false, false] * f ![false, true, true] =
      f ![false, false, true] * f ![false, true, false] := by
  obtain ⟨c, u, hu⟩ := h
  simp only [hu, Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one,
    Matrix.cons_val_zero, Matrix.cons_val_succ]
  ring

/-- Canonical ordered pairs (0,1), (2,3), (4,5). -/
def threePairs : Pairing 6 where
  count := 3
  ports := {
    toFun := fun jb => if jb.2 then ![1, 3, 5] jb.1 else ![0, 2, 4] jb.1
    invFun := fun k => ![(0, false), (0, true), (1, false), (1, true),
      (2, false), (2, true)] k
    left_inv := by decide +kernel
    right_inv := by decide +kernel }

theorem threePairs_transversal (x : Fin 6 → Bool) :
    Transversal threePairs x ↔
      x 1 = !(x 0) ∧ x 3 = !(x 2) ∧ x 5 = !(x 4) := by
  simp [Transversal, threePairs, Fin.forall_fin_succ]
  rfl

/-- Six-port two-level table produced by the final native-X closure in
Lemma 8.11. D occurs on the two antipodal choices; E on the other six. -/
def twoLevel (D E : K) : Signature K 6 := fun x =>
  if x 1 = !(x 0) ∧ x 3 = !(x 2) ∧ x 5 = !(x 4) then
    (if (x 0 = false ∧ x 2 = false ∧ x 4 = false) ∨
      (x 0 = true ∧ x 2 = true ∧ x 4 = true) then D else E) else 0

theorem twoLevel_ne_zero {D E : K} (hD : D ≠ 0) (hE : E ≠ 0)
    (x : Fin 6 → Bool) : twoLevel D E x ≠ 0 ↔ Transversal threePairs x := by
  rw [threePairs_transversal]
  simp only [twoLevel]
  split_ifs <;> simp_all

@[simp] theorem threePairs_word (z : Fin 3 → Bool) :
    word threePairs z = ![z 0, !(z 0), z 1, !(z 1), z 2, !(z 2)] := by
  ext k
  fin_cases k <;> simp [word_apply, threePairs, orient]

theorem twoLevel_choice (D E : K) (z : Fin 3 → Bool) :
    twoLevel D E (word threePairs z) =
      if (z 0 = false ∧ z 1 = false ∧ z 2 = false) ∨
        (z 0 = true ∧ z 1 = true ∧ z 2 = true) then D else E := by
  rw [threePairs_word]
  simp [twoLevel]
  rfl

/-- The deleted-antipodes case has six supported words. -/
theorem card_support_twoLevel_zero (E : K) (hE : E ≠ 0) :
    (Matching.support (twoLevel 0 E)).card = 6 := by
  classical
  let s := Finset.univ.filter (fun x : Fin 6 → Bool =>
    (x 1 = !(x 0) ∧ x 3 = !(x 2) ∧ x 5 = !(x 4)) ∧
    ¬ ((x 0 = false ∧ x 2 = false ∧ x 4 = false) ∨
      (x 0 = true ∧ x 2 = true ∧ x 4 = true)))
  have hs : Matching.support (twoLevel 0 E) = s := by
    ext x
    simp only [Matching.support, Finset.mem_filter, Finset.mem_univ, true_and, s]
    simp only [twoLevel]
    split_ifs <;> simp_all
  rw [hs]
  decide +kernel

/-- This excludes *every* weighted perfect matching. When D=0 the support
has six rather than eight words; otherwise its support fixes the port pairs,
and its unary-product minor forces D=E. -/
theorem twoLevel_not_isProduct {D E : K} (hE : E ≠ 0) (hDE : D ≠ E) :
    ¬ IsProduct (twoLevel D E) := by
  rintro ⟨Q, p, q, c, hnz, heq⟩
  by_cases hD : D = 0
  · subst D
    have hc := card_support_product Q p q c hnz
    have hcount := Matching.pair_count Q
    have hcount3 : Q.count = 3 := by omega
    rw [← heq, card_support_twoLevel_zero E hE, hcount3] at hc
    norm_num at hc
  · have hs : ∀ x, Transversal threePairs x ↔ Transversal Q x := by
      intro x
      rw [← twoLevel_ne_zero hD hE, heq, product_ne_zero Q p q c hnz]
    have hu := product_unary_of_same_support threePairs Q hs p q c
    have hm := unary_product_minor hu
    simp only [← heq, twoLevel_choice] at hm
    simp at hm
    exact hDE (hm.resolve_right hE)

end Paper2.WeightedMatching
