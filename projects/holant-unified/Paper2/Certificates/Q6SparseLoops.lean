import Paper2.Certificates.Q6Arrays
import Paper2.Certificates.Q6Sparse

namespace Paper2.Certificates.Q6
variable {K : Type*} [CommRing K] [NoZeroDivisors K]

theorem selected_loop_2_0 (u : Fin 8 → K)
    (hl : AllLoopSafe (fullOrbit u 2)) :
    NecessarySafe ![0 + (u 1), 0 + -(u 1), 0 + 0, 0 + 0, (u 0) + 0, -(u 0) + 0] := by
  have he : loopArray (fullOrbit u 2) (loopSpecs 0) = ![-(u 0) + 0, (u 0) + 0, 0 + 0, 0 + 0, 0 + -(u 1), 0 + (u 1)] := by
    funext e
    rw [loopArray_coordinates]
    fin_cases e <;> rfl
  have hs := hl 0
  rw [he] at hs
  exact hs.reverse

theorem selected_loop_3_0 (u : Fin 8 → K)
    (hl : AllLoopSafe (fullOrbit u 3)) :
    NecessarySafe ![0 + (u 2), 0 + (u 3), 0 + 0, 0 + 0, (u 0) + 0, (u 1) + 0] := by
  have he : loopArray (fullOrbit u 3) (loopSpecs 0) = ![(u 1) + 0, (u 0) + 0, 0 + 0, 0 + 0, 0 + (u 3), 0 + (u 2)] := by
    funext e
    rw [loopArray_coordinates]
    fin_cases e <;> rfl
  have hs := hl 0
  rw [he] at hs
  exact hs.reverse

theorem selected_loop_5_0 (u : Fin 8 → K)
    (hl : AllLoopSafe (fullOrbit u 5)) :
    NecessarySafe ![0 + (u 1), 0 + 0, (u 0) + -(u 1), (u 0) + -(u 1), 0 + 0, -(u 0) + 0] := by
  have he : loopArray (fullOrbit u 5) (loopSpecs 0) = ![-(u 0) + 0, 0 + 0, (u 0) + -(u 1), (u 0) + -(u 1), 0 + 0, 0 + (u 1)] := by
    funext e
    rw [loopArray_coordinates]
    fin_cases e <;> rfl
  have hs := hl 0
  rw [he] at hs
  exact hs.reverse

theorem selected_loop_6_0 (u : Fin 8 → K)
    (hl : AllLoopSafe (fullOrbit u 6)) :
    NecessarySafe ![0 + (u 2), 0 + 0, (u 0) + -(u 2), (u 1) + (u 3), 0 + 0, -(u 1) + 0] := by
  have he : loopArray (fullOrbit u 6) (loopSpecs 0) = ![-(u 1) + 0, 0 + 0, (u 1) + (u 3), (u 0) + -(u 2), 0 + 0, 0 + (u 2)] := by
    funext e
    rw [loopArray_coordinates]
    fin_cases e <;> rfl
  have hs := hl 0
  rw [he] at hs
  exact hs.reverse

theorem selected_loop_7_1 (u : Fin 8 → K)
    (hl : AllLoopSafe (fullOrbit u 7)) :
    NecessarySafe ![0 + (u 3), 0 + 0, 0 + (u 4), (u 1) + 0, 0 + 0, (u 2) + 0] := by
  have he : loopArray (fullOrbit u 7) (loopSpecs 1) = ![(u 2) + 0, 0 + 0, (u 1) + 0, 0 + (u 4), 0 + 0, 0 + (u 3)] := by
    funext e
    rw [loopArray_coordinates]
    fin_cases e <;> rfl
  have hs := hl 1
  rw [he] at hs
  exact hs.reverse

theorem selected_loop_7_2 (u : Fin 8 → K)
    (hl : AllLoopSafe (fullOrbit u 7)) :
    NecessarySafe ![0 + (u 3), 0 + (u 5), 0 + 0, 0 + 0, (u 0) + 0, (u 2) + 0] := by
  have he : loopArray (fullOrbit u 7) (loopSpecs 2) = ![(u 2) + 0, (u 0) + 0, 0 + 0, 0 + 0, 0 + (u 5), 0 + (u 3)] := by
    funext e
    rw [loopArray_coordinates]
    fin_cases e <;> rfl
  have hs := hl 2
  rw [he] at hs
  exact hs.reverse

theorem selected_loop_9_1 (u : Fin 8 → K)
    (hl : AllLoopSafe (fullOrbit u 9)) :
    NecessarySafe ![0 + 0, 0 + (u 3), 0 + (u 4), (u 1) + 0, (u 2) + 0, 0 + 0] := by
  have he : loopArray (fullOrbit u 9) (loopSpecs 1) = ![0 + 0, (u 2) + 0, (u 1) + 0, 0 + (u 4), 0 + (u 3), 0 + 0] := by
    funext e
    rw [loopArray_coordinates]
    fin_cases e <;> rfl
  have hs := hl 1
  rw [he] at hs
  exact hs.reverse

theorem selected_loop_10_1 (u : Fin 8 → K)
    (hl : AllLoopSafe (fullOrbit u 10)) :
    NecessarySafe ![0 + 0, 0 + (u 4), 0 + (u 5), (u 2) + 0, (u 3) + 0, 0 + 0] := by
  have he : loopArray (fullOrbit u 10) (loopSpecs 1) = ![0 + 0, (u 3) + 0, (u 2) + 0, 0 + (u 5), 0 + (u 4), 0 + 0] := by
    funext e
    rw [loopArray_coordinates]
    fin_cases e <;> rfl
  have hs := hl 1
  rw [he] at hs
  exact hs.reverse

theorem selected_loop_10_2 (u : Fin 8 → K)
    (hl : AllLoopSafe (fullOrbit u 10)) :
    NecessarySafe ![0 + 0, 0 + (u 6), 0 + (u 7), (u 0) + 0, (u 1) + 0, 0 + 0] := by
  have he : loopArray (fullOrbit u 10) (loopSpecs 2) = ![0 + 0, (u 1) + 0, (u 0) + 0, 0 + (u 7), 0 + (u 6), 0 + 0] := by
    funext e
    rw [loopArray_coordinates]
    fin_cases e <;> rfl
  have hs := hl 2
  rw [he] at hs
  exact hs.reverse

theorem selected_loop_20_0 (u : Fin 8 → K)
    (hl : AllLoopSafe (fullOrbit u 20)) :
    NecessarySafe ![-(u 0) + (u 0), (u 0) + (u 3), -(u 0) + (u 4), (u 1) + (u 0), (u 2) + -(u 0), -(u 0) + (u 0)] := by
  have he : loopArray (fullOrbit u 20) (loopSpecs 0) = ![-(u 0) + (u 0), (u 2) + -(u 0), (u 1) + (u 0), -(u 0) + (u 4), (u 0) + (u 3), -(u 0) + (u 0)] := by
    funext e
    rw [loopArray_coordinates]
    fin_cases e <;> rfl
  have hs := hl 0
  rw [he] at hs
  exact hs.reverse

end Paper2.Certificates.Q6
