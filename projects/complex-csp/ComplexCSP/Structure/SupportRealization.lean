import ComplexCSP.Instances.Basic
import ComplexCSP.Algebra.PowerSums
import ComplexCSP.Instances.OrderedInstances

/-! # Equality-free support realization

Power amplification removes cancellations uniformly across all boundary
assignments. This file uses the proved bounded power-sum theorem and actual
finite-instance gluing/powering/marginalization, not a closure oracle.
-/
namespace ComplexCSP
open scoped BigOperators

/-- One positive power makes every nonempty fibre sum nonzero simultaneously.
Empty fibres remain zero. This is the cancellation-control part of Lemma 7.2. -/
theorem exists_power_preserving_existential_support {R W K : Type}
    [Fintype R] [Fintype W] [CommRing K] [IsDomain K] [CharZero K]
    (F : R → W → K) :
    ∃ m : ℕ, 0 < m ∧ ∀ r, (∑ w, F r w ^ m) ≠ 0 ↔ ∃ w, F r w ≠ 0 := by
  classical
  let A := {r : R // ∃ w, F r w ≠ 0}
  let T (r : A) := {w : W // F r.val w ≠ 0}
  letI (r : A) : Nonempty (T r) := by
    obtain ⟨w, hw⟩ := r.property
    exact ⟨⟨w, hw⟩⟩
  obtain ⟨m, hm, _, hs⟩ := exists_simultaneous_powerSum_ne_zero_bounded
    (fun (r : A) (w : T r) => F r.val w.val) (fun _ w => w.property)
  refine ⟨m, hm, fun r => ?_⟩
  constructor
  · intro h
    by_contra! hz
    apply h
    simp [hz, zero_pow hm.ne']
  · intro hr
    let r' : A := ⟨r, hr⟩
    have he : (∑ w, F r w ^ m) = powerSum (fun w : T r' => F r w.val) m := by
      unfold powerSum
      rw [← Finset.sum_subtype (Finset.univ.filter (fun w => F r w ≠ 0))
        (by intro w; simp [r']) (fun w => F r w ^ m)]
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro w _ hw
      have hz : F r w = 0 := by simpa using hw
      simp [hz, zero_pow hm.ne']
    rw [he]
    exact hs r'

/-- A real terminating exact search for the common support-amplification power.
The ring operations and equality are supplied computational instances; there is
no installed classical equality and no oracle for the infinite generated family. -/
def findSupportPower {R W K : Type} [Fintype R] [Fintype W]
    [CommRing K] [IsDomain K] [CharZero K] [DecidableEq K] (F : R → W → K) : ℕ :=
  Nat.find (exists_power_preserving_existential_support F)

theorem findSupportPower_spec {R W K : Type} [Fintype R] [Fintype W]
    [CommRing K] [IsDomain K] [CharZero K] [DecidableEq K] (F : R → W → K) :
    0 < findSupportPower F ∧ ∀ r,
      (∑ w, F r w ^ findSupportPower F) ≠ 0 ↔ ∃ w, F r w ≠ 0 :=
  Nat.find_spec (exists_power_preserving_existential_support F)

namespace Instance
variable {D K ι B H : Type} {L : Language D K ι}

/-- Marginal support can be realized without adding equality constraints or
conjugated language symbols. All internal variables of power copies are fresh. -/
theorem generated_existential_support [Fintype D] [Fintype B] [DecidableEq B]
    [Fintype H] [DecidableEq H] [CommRing K] [IsDomain K] [CharZero K]
    {G : (B ⊕ H → D) → K} (hG : Generated L G) :
    ∃ F : (B → D) → K, Generated L F ∧
      ∀ a, F a ≠ 0 ↔ ∃ b : H → D, G (Sum.elim a b) ≠ 0 := by
  obtain ⟨m, hm, hs⟩ := exists_power_preserving_existential_support
    (fun (a : B → D) (b : H → D) => G (Sum.elim a b))
  refine ⟨fun a => ∑ b : H → D, G (Sum.elim a b) ^ m, ?_, hs⟩
  exact generated_marginal (generated_pow hG m)

/-- Literal finite equality-free conjunctions of generated support predicates
are generated supports. Each atom scope is an arbitrary map, so repeated
logical variables are allowed and no equality relation is added. -/
theorem generated_conjunction_support [Fintype D] [CommRing K] [IsDomain K]
    {A : Type} [Fintype A] (arity : A → ℕ)
    (G : (i : A) → (Fin (arity i) → D) → K)
    (hG : ∀ i, Generated L (G i)) (scope : (i : A) → Fin (arity i) → B) :
    ∃ F : (B → D) → K, Generated L F ∧
      ∀ a, F a ≠ 0 ↔ ∀ i, G i (a ∘ scope i) ≠ 0 := by
  classical
  refine ⟨fun a => ∏ i, G i (a ∘ scope i), ?_, ?_⟩
  · apply generated_finset_prod Finset.univ
    intro i _
    exact generated_diagonal_minor (hG i) (scope i)
  · intro a
    simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, forall_true_left]

/-- Lemma 7.2 in finite equality-free pp syntax: an existential conjunction of
finitely many generated supports is itself an actual generated support. -/
theorem generated_equalityfree_pp_support [Fintype D] [Fintype B] [DecidableEq B]
    [Fintype H] [DecidableEq H] [CommRing K] [IsDomain K] [CharZero K]
    {A : Type} [Fintype A] (arity : A → ℕ)
    (G : (i : A) → (Fin (arity i) → D) → K)
    (hG : ∀ i, Generated L (G i)) (scope : (i : A) → Fin (arity i) → B ⊕ H) :
    ∃ F : (B → D) → K, Generated L F ∧
      ∀ a, F a ≠ 0 ↔ ∃ b : H → D, ∀ i, G i (Sum.elim a b ∘ scope i) ≠ 0 := by
  obtain ⟨P, hP, hPsupp⟩ := generated_conjunction_support arity G hG scope
  obtain ⟨F, hF, hFsupp⟩ := generated_existential_support hP
  exact ⟨F, hF, fun a => by simp only [hFsupp, hPsupp]⟩

end Instance
/-- Paper Lemma 7.2 specialized to exactly the ordered generated-family
semantics and arbitrary finite conjunctions with repeated scope variables. -/
theorem paper_generated_equalityfree_pp_support
    {D K ι A : Type} [Fintype D] [Fintype A]
    [CommRing K] [IsDomain K] [CharZero K] {L : Language D K ι}
    {r h : ℕ} (arity : A → ℕ)
    (G : (i : A) → (Fin (arity i) → D) → K)
    (hG : ∀ i, PaperGenerated L (G i))
    (scope : (i : A) → Fin (arity i) → Fin r ⊕ Fin h) :
    ∃ F : (Fin r → D) → K, PaperGenerated L F ∧
      ∀ a, F a ≠ 0 ↔ ∃ b : Fin h → D, ∀ i,
        G i (Sum.elim a b ∘ scope i) ≠ 0 := by
  obtain ⟨F, hF, hFsupp⟩ := Instance.generated_equalityfree_pp_support
    arity G (fun i => (generated_iff_paperGenerated _).mpr (hG i)) scope
  exact ⟨F, (generated_iff_paperGenerated _).mp hF, hFsupp⟩

end ComplexCSP
