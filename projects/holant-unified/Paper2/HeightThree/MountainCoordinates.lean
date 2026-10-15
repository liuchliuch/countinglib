import Paper2.HeightThree.LoopGeometry
import Paper2.Mountain

namespace Paper2.HeightThree
open Certificates.Q6

variable {K : Type} [CommRing K]

def mountainCoefficients (M : Signature K 6) (i : Fin 20) : K := M (subsetWord (tripleSet i))

lemma coefficient_mountain_center (M : Signature K 6) (x : Port → Bool) (hx : weight x = 3) :
    coefficient (mountainCoefficients M) (mask (occupied x)) = M x := by
  have hcard : (occupied x).card = 3 := (occupied_card_weight x).trans hx
  obtain ⟨i,hi⟩ := tripleMasks_complete (occupied x) hcard
  have hset : occupied x = tripleSet i :=
    mask_injective (hi.trans (tripleSet_correct i).2.symm)
  rw [hi,coefficient_at_triple]
  unfold mountainCoefficients
  rw [← hset,subsetWord_occupied]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma occupied_constant_mask (b : Bool) : mask (occupied (fun _ : Port => b)) = (if b then 63 else 0) := by
  revert b
  decide +kernel

lemma coordinateMountain_false (a b : K) (q : Fin 20 → K) :
    coordinateMountain a b q (fun _ => false) = a := by
  have hn : (fun _ : Port => false) ≠ (fun _ => true) := by intro h; have := congrFun h 0; contradiction
  simp only [coordinateMountain,ite_true,hn,ite_false,occupied_constant_mask]
  simp [coefficient]

lemma coordinateMountain_true (a b : K) (q : Fin 20 → K) :
    coordinateMountain a b q (fun _ => true) = b := by
  have hn : (fun _ : Port => true) ≠ (fun _ => false) := by intro h; have := congrFun h 0; contradiction
  simp only [coordinateMountain,hn,ite_false,ite_true,occupied_constant_mask]
  simp [coefficient]

/-- Every literal height-three mountain is represented by its actual endpoint
entries and its twenty actual central coefficients. -/
theorem mountain_coordinate_decomposition (M : Signature K 6) (hM : IsMountain (d := 3) M) :
    M = coordinateMountain (M (fun _ => false)) (M (fun _ => true)) (mountainCoefficients M) := by
  funext x
  by_cases hx0 : x = (fun _ => false)
  · subst x
    exact (coordinateMountain_false _ _ _).symm
  by_cases hx1 : x = (fun _ => true)
  · subst x
    exact (coordinateMountain_true _ _ _).symm
  by_cases hxc : weight x = 3
  · simp only [coordinateMountain,hx0,hx1,ite_false,zero_add,
      coefficient_mountain_center M x hxc]
  · have hmz : M x = 0 := by
      by_contra hz
      rcases hM.support_layers x hz with h | h | h
      · exact hx0 h
      · have hh : (weight x : ℤ) - 3 = 0 := h
        omega
      · exact hx1 h
    have hcard : (occupied x).card ≠ 3 := by rw [occupied_card_weight]; exact hxc
    simp only [coordinateMountain,hx0,hx1,ite_false,zero_add,
      coefficient_mask_zero _ _ hcard,hmz]

end Paper2.HeightThree
