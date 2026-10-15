import Paper2.Certificates.Q6CoverageCompact.Terminal
namespace Paper2.Certificates.Q6.Coverage
/-- Every actual coefficient vector satisfying the fifteen complementary-zero
loop conditions lies in an explicitly transported official parameter row. -/
theorem compact_exhaustive_cover {K : Type*} [CommRing K] [NoZeroDivisors K] [CharZero K]
    (q : Fin 20 → K) (h : ∀ d : Fin 15, ∃ b : Fin 3, (loopOptions d b).Holds q) :
    InOrbits officialRows q := by
  have h0 : Covered q layer0 := ⟨0, satisfies_initial q⟩
  have h1 := covered_step q layer0 layer1 next1 (loopOptions 0) transition1 h0 (h 0)
  have h2 := covered_step q layer1 layer2 next2 (loopOptions 1) transition2 h1 (h 1)
  have h3 := covered_step q layer2 layer3 next3 (loopOptions 2) transition3 h2 (h 2)
  have h4 := covered_step q layer3 layer4 next4 (loopOptions 3) transition4 h3 (h 3)
  have h5 := covered_step q layer4 layer5 next5 (loopOptions 4) transition5 h4 (h 4)
  have h6 := covered_step q layer5 layer6 next6 (loopOptions 5) transition6 h5 (h 5)
  have h7 := covered_step q layer6 layer7 next7 (loopOptions 6) transition7 h6 (h 6)
  have h8 := covered_step q layer7 layer8 next8 (loopOptions 7) transition8 h7 (h 7)
  have h9 := covered_step q layer8 layer9 next9 (loopOptions 8) transition9 h8 (h 8)
  have h10 := covered_step q layer9 layer10 next10 (loopOptions 9) transition10 h9 (h 9)
  have h11 := covered_step q layer10 layer11 next11 (loopOptions 10) transition11 h10 (h 10)
  have h12 := covered_step q layer11 layer12 next12 (loopOptions 11) transition12 h11 (h 11)
  have h13 := covered_step q layer12 layer13 next13 (loopOptions 12) transition13 h12 (h 12)
  have h14 := covered_step q layer13 layer14 next14 (loopOptions 13) transition14 h13 (h 13)
  have h15 := covered_step q layer14 layer15 next15 (loopOptions 14) transition15 h14 (h 14)
  exact terminal_covered q h15
end Paper2.Certificates.Q6.Coverage
