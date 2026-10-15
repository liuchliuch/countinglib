import Paper2.Bell
import Paper2.ReedMuller
import Paper2.Tractable.Criteria
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! Oriented Bell and X matching products, separate from the source's
K-onehot tractability closure. The pairing uses the shared explicit port
bijection, retaining every pair's orientation and the overall nonzero scalar. -/
namespace Paper2.Matching

abbrev Pairing := Tractable.OrientedPerfectPairing

variable {K : Type*} [CommRing K] [IsDomain K]

/-- An actual Bell matching tensor, with explicitly ordered pair factors. -/
def bellProduct {n : ℕ} (p : Pairing n) (d l : Fin p.count → Bool)
    (c : K) : Signature K n := fun x =>
  c * ∏ j : Fin p.count,
    Bell.ordered (d j) (l j) (x (p.ports (j, false))) (x (p.ports (j, true)))

def IsBellProduct {n : ℕ} (f : Signature K n) : Prop :=
  ∃ (p : Pairing n) (d l : Fin p.count → Bool) (c : K),
    c ≠ 0 ∧ f = bellProduct p d l c

def IsXMatchingProduct {n : ℕ} (f : Signature K n) : Prop :=
  ∃ (p : Pairing n) (c : K), c ≠ 0 ∧
    f = bellProduct p (fun _ => true) (fun _ => false) c

omit [IsDomain K] in
theorem xMatching_is_bell {n : ℕ} {f : Signature K n}
    (h : IsXMatchingProduct f) : IsBellProduct f := by
  obtain ⟨p, c, hc, rfl⟩ := h
  exact ⟨p, _, _, c, hc, rfl⟩

/-- Encode the independently chosen first endpoint of every pair. -/
def word {n : ℕ} (p : Pairing n) (d z : Fin p.count → Bool) : Fin n → Bool :=
  fun k => let jb := p.ports.symm k
    if jb.2 then Bool.xor (z jb.1) (d jb.1) else z jb.1

@[simp] theorem word_first {n : ℕ} (p : Pairing n) (d z : Fin p.count → Bool)
    (j : Fin p.count) : word p d z (p.ports (j, false)) = z j := by simp [word]

@[simp] theorem word_second {n : ℕ} (p : Pairing n) (d z : Fin p.count → Bool)
    (j : Fin p.count) : word p d z (p.ports (j, true)) = Bool.xor (z j) (d j) := by
  simp [word]

theorem word_injective {n : ℕ} (p : Pairing n) (d : Fin p.count → Bool) :
    Function.Injective (word p d) := by
  intro a b hab
  funext j
  simpa only [word_first] using congrFun hab (p.ports (j, false))

theorem bell_ne_zero (d l a b : Bool) :
    Bell.ordered (K := K) d l a b ≠ 0 ↔ Bool.xor a b = d := by
  cases d <;> cases l <;> cases a <;> cases b <;> simp [Bell.ordered, Bell.sign]

theorem product_ne_zero {n : ℕ} (p : Pairing n) (d l : Fin p.count → Bool)
    (c : K) (hc : c ≠ 0) (x : Fin n → Bool) :
    bellProduct p d l c x ≠ 0 ↔
      ∀ j, Bool.xor (x (p.ports (j, false))) (x (p.ports (j, true))) = d j := by
  simp [bellProduct, hc, Finset.prod_ne_zero_iff, bell_ne_zero]

theorem pair_constraints_iff_word {n : ℕ} (p : Pairing n) (d : Fin p.count → Bool)
    (x : Fin n → Bool) :
    (∀ j, Bool.xor (x (p.ports (j, false))) (x (p.ports (j, true))) = d j) ↔
      ∃ z, word p d z = x := by
  constructor
  · intro hx
    refine ⟨fun j => x (p.ports (j, false)), ?_⟩
    funext k
    obtain ⟨⟨j, b⟩, rfl⟩ := p.ports.surjective k
    cases b
    · simp only [word_first]
    · simp only [word_second]
      have h := hx j
      cases ha : x (p.ports (j, false)) <;>
        cases hb : x (p.ports (j, true)) <;> cases hd : d j <;> simp_all
  · rintro ⟨z, rfl⟩ j
    simp only [word_first, word_second]
    cases hz : z j <;> cases hd : d j <;> rfl

noncomputable def support {n : ℕ} (f : Signature K n) : Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter (fun x => f x ≠ 0)

theorem support_bellProduct {n : ℕ} (p : Pairing n) (d l : Fin p.count → Bool)
    (c : K) (hc : c ≠ 0) :
    support (bellProduct p d l c) = Finset.univ.image (word p d) := by
  classical
  ext x
  simp only [support, Finset.mem_filter, Finset.mem_univ, true_and,
    product_ne_zero p d l c hc, pair_constraints_iff_word, Finset.mem_image]

theorem card_support_bellProduct {n : ℕ} (p : Pairing n) (d l : Fin p.count → Bool)
    (c : K) (hc : c ≠ 0) : (support (bellProduct p d l c)).card = 2^p.count := by
  classical
  rw [support_bellProduct p d l c hc,
    Finset.card_image_of_injective _ (word_injective p d)]
  simp

theorem pair_count {n : ℕ} (p : Pairing n) : p.count * 2 = n := by
  have h := Fintype.card_congr p.ports
  simpa using h

theorem card_support_central : (support (ReedMuller.central (K := K))).card = 14 := by
  classical
  have h : support (ReedMuller.central (K := K)) =
      ReedMuller.code.filter (fun x => ReedMuller.weight x = 4) := by
    ext x
    simp only [support, Finset.mem_filter, Finset.mem_univ, true_and, ReedMuller.mem_code]
    change (ReedMuller.central (K := K) x ≠ 0) ↔ ReedMuller.IsCentral x
    by_cases hx : ReedMuller.IsCentral x <;> simp [ReedMuller.central, hx]
  rw [h, ReedMuller.card_central]

/-- The central RM8 exception has fourteen supported words, whereas every
nonzero four-pair Bell product has sixteen; arbitrary orientations are covered. -/
theorem central_not_bellProduct : ¬ IsBellProduct (ReedMuller.central (K := K)) := by
  rintro ⟨p, d, l, c, hc, heq⟩
  have hp := pair_count p
  have hcount : p.count = 4 := by omega
  have hcard := card_support_bellProduct p d l c hc
  rw [← heq, card_support_central, hcount] at hcard
  norm_num at hcard

theorem central_not_xMatchingProduct :
    ¬ IsXMatchingProduct (ReedMuller.central (K := K)) :=
  fun h => central_not_bellProduct (xMatching_is_bell h)

end Paper2.Matching
