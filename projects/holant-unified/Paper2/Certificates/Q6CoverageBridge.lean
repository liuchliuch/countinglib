import Paper2.Certificates.Q6Arrays
import Paper2.Certificates.Q6Coverage.Data00
import Paper2.Certificates.Q6Coverage.Rows

/-! Exact bridges between the actual loop arrays, the signed-equation DAG,
and the compact scalar parameterization of all twenty-four rows. -/
namespace Paper2.Certificates.Q6

open Coverage

def complementaryEntry : Fin 3 → Fin 6 × Fin 6 := ![(0,5),(1,4),(2,3)]

variable {K : Type*} [CommRing K] [NoZeroDivisors K]

theorem NecessarySafe.zero_pair {v : Fin 6 → K} (h : NecessarySafe v) :
    ∃ b : Fin 3, v (complementaryEntry b).1 = 0 ∧ v (complementaryEntry b).2 = 0 := by
  rcases h.zeroProduct with hz | hz | hz
  · refine ⟨0, ?_⟩
    rcases mul_eq_zero.mp hz with hz | hz
    · exact ⟨hz,h.zero05.mp hz⟩
    · exact ⟨h.zero05.mpr hz,hz⟩
  · refine ⟨1, ?_⟩
    rcases mul_eq_zero.mp hz with hz | hz
    · exact ⟨hz,h.zero14.mp hz⟩
    · exact ⟨h.zero14.mpr hz,hz⟩
  · refine ⟨2, ?_⟩
    rcases mul_eq_zero.mp hz with hz | hz
    · exact ⟨hz,h.zero23.mp hz⟩
    · exact ⟨h.zero23.mpr hz,hz⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem loop_options_match (i : Fin 15) (b : Fin 3) :
    loopOptions i b = (loopCoordinatePairs i (complementaryEntry b).1,
      loopCoordinatePairs i (complementaryEntry b).2) := by
  revert i b
  decide +kernel

theorem allLoopSafe_branches (q : Fin 20 → K) (h : AllLoopSafe q) :
    ∀ i : Fin 15, ∃ b : Fin 3, (loopOptions i b).Holds q := by
  intro i
  obtain ⟨b,hb⟩ := (h i).zero_pair
  refine ⟨b, ?_⟩
  rw [loop_options_match]
  change (q (loopCoordinatePairs i (complementaryEntry b).1).1 +
    q (loopCoordinatePairs i (complementaryEntry b).1).2 = 0) ∧
    (q (loopCoordinatePairs i (complementaryEntry b).2).1 +
    q (loopCoordinatePairs i (complementaryEntry b).2).2 = 0)
  simpa only [loopArray_coordinates] using hb

/-- Official root indices, padded by zero after the row's independent roots. -/
def compactRoots : Fin 24 → Fin 8 → Fin 20 :=
  ![![0, 0, 0, 0, 0, 0, 0, 0], ![9, 10, 0, 0, 0, 0, 0, 0], ![8, 10, 0, 0, 0, 0, 0, 0], ![8, 9, 10, 11, 0, 0, 0, 0], ![6, 0, 0, 0, 0, 0, 0, 0], ![6, 10, 0, 0, 0, 0, 0, 0], ![6, 7, 10, 13, 0, 0, 0, 0], ![6, 7, 9, 10, 12, 13, 0, 0], ![5, 8, 11, 12, 0, 0, 0, 0], ![5, 7, 8, 11, 12, 13, 0, 0], ![5, 6, 7, 8, 11, 12, 13, 14], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 7, 12, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 7, 11, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0], ![0, 9, 10, 0, 0, 0, 0, 0], ![0, 7, 11, 0, 0, 0, 0, 0], ![0, 7, 8, 11, 12, 0, 0, 0], ![0, 5, 0, 0, 0, 0, 0, 0], ![0, 4, 9, 0, 0, 0, 0, 0], ![0, 4, 9, 10, 0, 0, 0, 0]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 2000000 in
omit [NoZeroDivisors K] in
theorem officialRows_eval_compact (p : Fin 20 → K) (r : Fin 24) :
    (fun i => (officialRows r i).eval p) = fullOrbit (fun j => p (compactRoots r j)) r := by
  funext i
  fin_cases r <;> fin_cases i <;> rfl

omit [NoZeroDivisors K] in
theorem inOrbits_compact (q : Fin 20 → K) (h : InOrbits officialRows q) :
    ∃ (r : Fin 24) (a : Action) (u : Fin 8 → K),
      a.Valid ∧ ∀ i, q (a.coords i) = fullOrbit u r i := by
  obtain ⟨r,a,p,ha,hp⟩ := h
  refine ⟨r,a,fun j => p (compactRoots r j),ha,?_⟩
  intro i
  rw [hp i]
  exact congrFun (officialRows_eval_compact p r) i

end Paper2.Certificates.Q6
