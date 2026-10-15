import Paper2.Certificates.Q6Coverage
import Paper2.Certificates.Q6OrbitReduction
import Paper2.Certificates.Q6LoopNaturality
import Paper2.Certificates.Q6CardAction

/-! Appendix A.4: exact joint-loop/two-copy-array support theorem.
Every premise refers to the actual finite array definitions. Exhaustive signed
branch coverage, row algebra, and orbit naturality are proved separately. -/
namespace Paper2.Certificates.Q6

variable {K : Type*} [CommRing K] [NoZeroDivisors K] [CharZero K]

/-- Every safe six-port joint deck has at most one complementary pair of
weight-three coefficients. No solver output or projective-chart assumption
appears in the hypotheses. -/
theorem joint_deck_support (q : Fin 20 → K) (t : K) (ht : t ≠ 0)
    (hl : AllLoopSafe q) (hc : AllTwoCopySafe q t) : OneComplementPair q := by
  have hcover := Coverage.exhaustive_cover q (allLoopSafe_branches q hl)
  obtain ⟨r,a,u,ha,hr⟩ := inOrbits_compact q hcover
  have hq : (fun i => q (a.coords i)) = fullOrbit u r := funext hr
  have hloop := AllLoopSafe.action q hl a ha
  have hcard := AllTwoCopySafe.action q t hc a ha
  rw [hq] at hloop hcard
  have hs := all_orbits_one_complement_pair u t ht r hloop hcard
  apply OneComplementPair.of_action q a ha
  rw [hq]
  exact hs

end Paper2.Certificates.Q6
