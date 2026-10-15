import Paper2.HeightOne.Cyclic.MatchingPencil

/-! Literal perfect-matching equality codes in the cyclic Walsh coordinates,
with their exact cardinality and the source phase-independent matching result. -/
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable
variable {K : Type*} [Field K]

abbrev Pairing := OrientedPerfectPairing

def equalityCode {n : ℕ} (P : Pairing n) : Finset (Word (Fin n)) := by
  classical
  exact Finset.univ.filter (fun x => ∀ j, x (P.ports (j, false)) = x (P.ports (j, true)))

@[simp] lemma mem_equalityCode {n : ℕ} (P : Pairing n) (x : Word (Fin n)) :
    x ∈ equalityCode P ↔ ∀ j, x (P.ports (j, false)) = x (P.ports (j, true)) := by
  classical
  simp [equalityCode]

lemma equalityCode_xorClosed {n : ℕ} (P : Pairing n) : XorClosed (equalityCode P) := by
  intro x hx y hy
  rw [mem_equalityCode] at hx hy ⊢
  intro j
  simp only [xorWord, hx j, hy j]

lemma equalityCode_eq_image {n : ℕ} (P : Pairing n) :
    equalityCode P = Finset.univ.image (Matching.word P (fun _ => false)) := by
  classical
  ext x
  simp only [mem_equalityCode, Finset.mem_image, Finset.mem_univ, true_and]
  rw [← Matching.pair_constraints_iff_word]
  constructor <;> intro h j <;> have hj := h j <;>
    cases ha : x (P.ports (j, false)) <;> cases hb : x (P.ports (j, true)) <;> simp_all

lemma equalityCode_card {n : ℕ} (P : Pairing n) : (equalityCode P).card = 2 ^ (n / 2) := by
  classical
  rw [equalityCode_eq_image, Finset.card_image_of_injective _ (Matching.word_injective _ _)]
  have hp : P.count = n / 2 := by have := Matching.pair_count P; omega
  simp [hp]

lemma pencil_two_zeros (A B : Word (Fin 0) → K) {s t : K} (hst : s ≠ t)
    (hs : pencil A B s = 0) (ht : pencil A B t = 0) : A = 0 ∧ B = 0 := by
  constructor <;> funext x
  · exact (affine_two_roots hst (congrFun hs x) (congrFun ht x)).1
  · exact (affine_two_roots hst (congrFun hs x) (congrFun ht x)).2

/-- Source phase-independent matching lemma, including a zero pencil member
and the three-phase boundary case. Matching hypotheses concern each card
separately; the common matching is a conclusion. -/
theorem phase_independent_matching {n : ℕ} (A B : Word (Fin n) → K) (S : Set K)
    (hthree : ∃ s ∈ S, ∃ t ∈ S, ∃ u ∈ S, s ≠ t ∧ s ≠ u ∧ t ≠ u)
    (hmatching : ∀ s ∈ S, pencil A B s ≠ 0 → ∃ P : Pairing n,
      support (pencil A B s) = equalityCode P) :
    (A = 0 ∧ B = 0) ∨ ∃ P : Pairing n,
      (∀ s ∈ S, pencil A B s ≠ 0 → support (pencil A B s) = equalityCode P) ∧
      (∀ s ∈ S, ∀ t ∈ S, pencil A B s = 0 → pencil A B t = 0 → s = t) := by
  classical
  have hzeros {s t : K} (hst : s ≠ t) (hs : pencil A B s = 0) (ht : pencil A B t = 0) :
      A = 0 ∧ B = 0 := by
    constructor <;> funext x
    · exact (affine_two_roots hst (congrFun hs x) (congrFun ht x)).1
    · exact (affine_two_roots hst (congrFun hs x) (congrFun ht x)).2
  by_cases hnonzero : ∃ s ∈ S, pencil A B s ≠ 0
  · obtain ⟨s, hs, hn⟩ := hnonzero
    obtain ⟨P, hP⟩ := hmatching s hs hn
    right
    refine ⟨P, ?_, ?_⟩
    · intro t ht htn
      have hconst := pencil_support_constant A B S hthree
        (fun u hu hun => by
          obtain ⟨Q, hQ⟩ := hmatching u hu hun
          rw [hQ]
          exact equalityCode_xorClosed Q)
        (2 ^ (n / 2)) (fun u hu hun => by
          obtain ⟨Q, hQ⟩ := hmatching u hu hun
          rw [hQ, equalityCode_card])
      exact (hconst t ht s hs htn hn).trans hP
    · intro t ht u hu ht0 hu0
      by_contra htu
      obtain ⟨hA, hB⟩ := hzeros htu ht0 hu0
      apply hn
      funext x
      simp [pencil, hA, hB]
  · left
    obtain ⟨s, hs, t, ht, u, hu, hst, hsu, htu⟩ := hthree
    apply hzeros hst
    · by_contra h
      exact hnonzero ⟨s, hs, h⟩
    · by_contra h
      exact hnonzero ⟨t, ht, h⟩

end
end Paper2.HeightOne.Cyclic
