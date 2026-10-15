import Paper2.HeightThree.LoopGeometry
import Paper2.HeightThree.MatchingSafety

namespace Paper2.HeightThree
open Certificates.Q6

/-- For each triple coefficient, one literal loop exposes it with a unique
extension; the complementary coefficient goes to the complementary EO word. -/
def revealingLoop : Fin 20 → Fin 15 × Fin 6 :=
  ![(2,5), (1,5), (1,4), (1,3), (0,5), (0,4), (0,3), (0,2), (0,1), (0,0), (0,5), (0,4), (0,3), (0,2), (0,1), (0,0), (1,2), (1,1), (1,0), (2,0)]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma revealingLoop_coordinates (i : Fin 20) :
    let j := (revealingLoop i).1
    let e := (revealingLoop i).2
    ((loopCoordinatePairs j e).1 = i ∧ (loopCoordinatePairs j e).2 ≠ i ∧
      (loopCoordinatePairs j e).2 ≠ complementCoord i) ∨
    ((loopCoordinatePairs j e).2 = i ∧ (loopCoordinatePairs j e).1 ≠ i ∧
      (loopCoordinatePairs j e).1 ≠ complementCoord i) := by
  revert i
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma revealingLoop_off_pair (i : Fin 20) (e : Fin 6)
    (h : e ≠ (revealingLoop i).2 ∧ e ≠ entryComplement (revealingLoop i).2) :
    (loopCoordinatePairs (revealingLoop i).1 e).1 ≠ i ∧
    (loopCoordinatePairs (revealingLoop i).1 e).1 ≠ complementCoord i ∧
    (loopCoordinatePairs (revealingLoop i).1 e).2 ≠ i ∧
    (loopCoordinatePairs (revealingLoop i).1 e).2 ≠ complementCoord i := by
  revert i e
  decide +kernel

variable {K : Type*} [AddMonoid K]

lemma revealingLoop_value (q : Fin 20 → K) (i : Fin 20)
    (hq : ∀ j, q j ≠ 0 → j = i ∨ j = complementCoord i) :
    loopArray q (loopSpecs (revealingLoop i).1) (revealingLoop i).2 = q i := by
  rw [loopArray_coordinates]
  rcases revealingLoop_coordinates i with h | h
  · have hz : q (loopCoordinatePairs (revealingLoop i).1 (revealingLoop i).2).2 = 0 := by
      by_contra hne
      rcases hq _ hne with he | he
      · exact h.2.1 he
      · exact h.2.2 he
    rw [h.1,hz,add_zero]
  · have hz : q (loopCoordinatePairs (revealingLoop i).1 (revealingLoop i).2).1 = 0 := by
      by_contra hne
      rcases hq _ hne with he | he
      · exact h.2.1 he
      · exact h.2.2 he
    rw [h.1,hz,zero_add]

lemma revealingLoop_zero (q : Fin 20 → K) (i : Fin 20)
    (hq : ∀ j, q j ≠ 0 → j = i ∨ j = complementCoord i)
    (e : Fin 6) (he : e ≠ (revealingLoop i).2 ∧ e ≠ entryComplement (revealingLoop i).2) :
    loopArray q (loopSpecs (revealingLoop i).1) e = 0 := by
  rw [loopArray_coordinates]
  have h := revealingLoop_off_pair i e he
  have h₁ : q (loopCoordinatePairs (revealingLoop i).1 e).1 = 0 := by
    by_contra hn
    exact (hq _ hn).elim h.1 h.2.1
  have h₂ : q (loopCoordinatePairs (revealingLoop i).1 e).2 = 0 := by
    by_contra hn
    exact (hq _ hn).elim h.2.2.1 h.2.2.2
  rw [h₁,h₂,zero_add]

end Paper2.HeightThree
