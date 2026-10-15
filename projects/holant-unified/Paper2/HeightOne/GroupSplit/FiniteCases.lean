import Paper2.HeightOne.GroupSplit.CyclicDihedral
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

/-! Elementary permutation-group eliminations needed by Theorem 5.4.
Finite checking uses Lean kernel reduction. -/
namespace Paper2.HeightOne.GroupSplit

abbrev A4 := alternatingGroup (Fin 4)
abbrev S4 := Equiv.Perm (Fin 4)
abbrev A5 := alternatingGroup (Fin 5)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma s4_extra_even_involution (z : S4) (hz : z * z = 1) (hne : z ≠ 1) :
    ∃ u : S4, u * u = 1 ∧ u ≠ 1 ∧ u ≠ z ∧
      u * z = z * u ∧ u ∈ alternatingGroup (Fin 4) := by
  have h : ∀ z : S4, z * z = 1 → z ≠ 1 →
    ∃ u : S4, u * u = 1 ∧ u ≠ 1 ∧ u ≠ z ∧ u * z = z * u ∧
      Equiv.Perm.sign u = 1 := by decide +kernel
  simpa only [Equiv.Perm.mem_alternatingGroup] using h z hz hne

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma a4_extra_involution (z : A4) (hz : z * z = 1) (hne : z ≠ 1) :
    ∃ u : A4, u * u = 1 ∧ u ≠ 1 ∧ u ≠ z ∧ u * z = z * u := by
  have h : ∀ z : A4, z * z = 1 → z ≠ 1 →
    ∃ u : A4, u * u = 1 ∧ u ≠ 1 ∧ u ≠ z ∧ u * z = z * u := by decide +kernel
  exact h z hz hne

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma a5_extra_involution (z : A5) (hz : z * z = 1) (hne : z ≠ 1) :
    ∃ u : A5, u * u = 1 ∧ u ≠ 1 ∧ u ≠ z ∧ u * z = z * u := by
  have h : ∀ z : A5, z * z = 1 → z ≠ 1 →
    ∃ u : A5, u * u = 1 ∧ u ≠ 1 ∧ u ≠ z ∧ u * z = z * u := by decide +kernel
  exact h z hz hne


/- No index-two subgroup in the actual A4. The finite identity is checked by
kernel reduction; the index argument is ordinary group theory. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma a4_no_index_two (H : Subgroup A4) : H.index ≠ 2 := by
  intro hi
  have h3 : ∀ g : A4, g ^ 3 = 1 → g ∈ H := by
    intro g hg
    have h2 := H.mul_self_mem_of_index_two hi g
    apply (H.mul_mem_cancel_left h2).mp
    have he : (g * g) * g = 1 := by simpa [pow_succ, pow_two] using hg
    rw [he]
    exact H.one_mem
  have hex : ∀ g : A4, ∃ a b : A4, a ^ 3 = 1 ∧ b ^ 3 = 1 ∧ g = a * b := by
    decide +kernel
  have ht : H = ⊤ := by
    apply top_unique
    intro g _
    obtain ⟨a, b, ha, hb, rfl⟩ := hex g
    exact H.mul_mem (h3 a ha) (h3 b hb)
  simp [ht] at hi

lemma a5_no_index_two (H : Subgroup A5) : H.index ≠ 2 := by
  intro h
  letI : IsSimpleGroup A5 := alternatingGroup.isSimpleGroup (by simp)
  rcases (Subgroup.normal_of_index_eq_two h).eq_bot_or_eq_top with he | he
  · rw [he, Subgroup.index_bot] at h
    have hc : Nat.card A5 = 60 := by rw [nat_card_alternatingGroup]; norm_num [Nat.factorial]
    omega
  · simp [he] at h

end Paper2.HeightOne.GroupSplit
