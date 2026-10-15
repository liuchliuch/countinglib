import Paper2.Certificates.Q6CoverageCompact.WitnessCheck29

namespace Paper2.Certificates.Q6.Coverage

theorem checkedTerminalPrefix128 : checkRange checkTerminalAt 0 128 = true :=
  checkRange_join checkTerminalAt 0 64 64 checkedTerminal_0_64 checkedTerminal_64_64

theorem checkedTerminalPrefix192 : checkRange checkTerminalAt 0 192 = true :=
  checkRange_join checkTerminalAt 0 128 64 checkedTerminalPrefix128 checkedTerminal_128_64

theorem checkedTerminalPrefix256 : checkRange checkTerminalAt 0 256 = true :=
  checkRange_join checkTerminalAt 0 192 64 checkedTerminalPrefix192 checkedTerminal_192_64

theorem checkedTerminalPrefix320 : checkRange checkTerminalAt 0 320 = true :=
  checkRange_join checkTerminalAt 0 256 64 checkedTerminalPrefix256 checkedTerminal_256_64

theorem checkedTerminalPrefix384 : checkRange checkTerminalAt 0 384 = true :=
  checkRange_join checkTerminalAt 0 320 64 checkedTerminalPrefix320 checkedTerminal_320_64

theorem checkedTerminalPrefix448 : checkRange checkTerminalAt 0 448 = true :=
  checkRange_join checkTerminalAt 0 384 64 checkedTerminalPrefix384 checkedTerminal_384_64

theorem checkedTerminalPrefix512 : checkRange checkTerminalAt 0 512 = true :=
  checkRange_join checkTerminalAt 0 448 64 checkedTerminalPrefix448 checkedTerminal_448_64

theorem checkedTerminalPrefix576 : checkRange checkTerminalAt 0 576 = true :=
  checkRange_join checkTerminalAt 0 512 64 checkedTerminalPrefix512 checkedTerminal_512_64

theorem checkedTerminalPrefix640 : checkRange checkTerminalAt 0 640 = true :=
  checkRange_join checkTerminalAt 0 576 64 checkedTerminalPrefix576 checkedTerminal_576_64

theorem checkedTerminalPrefix704 : checkRange checkTerminalAt 0 704 = true :=
  checkRange_join checkTerminalAt 0 640 64 checkedTerminalPrefix640 checkedTerminal_640_64

theorem checkedTerminalPrefix768 : checkRange checkTerminalAt 0 768 = true :=
  checkRange_join checkTerminalAt 0 704 64 checkedTerminalPrefix704 checkedTerminal_704_64

theorem checkedTerminalPrefix832 : checkRange checkTerminalAt 0 832 = true :=
  checkRange_join checkTerminalAt 0 768 64 checkedTerminalPrefix768 checkedTerminal_768_64

theorem checkedTerminalPrefix896 : checkRange checkTerminalAt 0 896 = true :=
  checkRange_join checkTerminalAt 0 832 64 checkedTerminalPrefix832 checkedTerminal_832_64

theorem checkedTerminalPrefix960 : checkRange checkTerminalAt 0 960 = true :=
  checkRange_join checkTerminalAt 0 896 64 checkedTerminalPrefix896 checkedTerminal_896_64

theorem checkedTerminalPrefix1024 : checkRange checkTerminalAt 0 1024 = true :=
  checkRange_join checkTerminalAt 0 960 64 checkedTerminalPrefix960 checkedTerminal_960_64

theorem checkedTerminalPrefix1088 : checkRange checkTerminalAt 0 1088 = true :=
  checkRange_join checkTerminalAt 0 1024 64 checkedTerminalPrefix1024 checkedTerminal_1024_64

theorem checkedTerminalPrefix1152 : checkRange checkTerminalAt 0 1152 = true :=
  checkRange_join checkTerminalAt 0 1088 64 checkedTerminalPrefix1088 checkedTerminal_1088_64

theorem checkedTerminalPrefix1216 : checkRange checkTerminalAt 0 1216 = true :=
  checkRange_join checkTerminalAt 0 1152 64 checkedTerminalPrefix1152 checkedTerminal_1152_64

theorem checkedTerminalPrefix1280 : checkRange checkTerminalAt 0 1280 = true :=
  checkRange_join checkTerminalAt 0 1216 64 checkedTerminalPrefix1216 checkedTerminal_1216_64

theorem checkedTerminalPrefix1344 : checkRange checkTerminalAt 0 1344 = true :=
  checkRange_join checkTerminalAt 0 1280 64 checkedTerminalPrefix1280 checkedTerminal_1280_64

theorem checkedTerminalPrefix1408 : checkRange checkTerminalAt 0 1408 = true :=
  checkRange_join checkTerminalAt 0 1344 64 checkedTerminalPrefix1344 checkedTerminal_1344_64

theorem checkedTerminalPrefix1472 : checkRange checkTerminalAt 0 1472 = true :=
  checkRange_join checkTerminalAt 0 1408 64 checkedTerminalPrefix1408 checkedTerminal_1408_64

theorem checkedTerminalPrefix1536 : checkRange checkTerminalAt 0 1536 = true :=
  checkRange_join checkTerminalAt 0 1472 64 checkedTerminalPrefix1472 checkedTerminal_1472_64

theorem checkedTerminalPrefix1600 : checkRange checkTerminalAt 0 1600 = true :=
  checkRange_join checkTerminalAt 0 1536 64 checkedTerminalPrefix1536 checkedTerminal_1536_64

theorem checkedTerminalPrefix1664 : checkRange checkTerminalAt 0 1664 = true :=
  checkRange_join checkTerminalAt 0 1600 64 checkedTerminalPrefix1600 checkedTerminal_1600_64

theorem checkedTerminalPrefix1728 : checkRange checkTerminalAt 0 1728 = true :=
  checkRange_join checkTerminalAt 0 1664 64 checkedTerminalPrefix1664 checkedTerminal_1664_64

theorem checkedTerminalPrefix1792 : checkRange checkTerminalAt 0 1792 = true :=
  checkRange_join checkTerminalAt 0 1728 64 checkedTerminalPrefix1728 checkedTerminal_1728_64

theorem checkedTerminalPrefix1856 : checkRange checkTerminalAt 0 1856 = true :=
  checkRange_join checkTerminalAt 0 1792 64 checkedTerminalPrefix1792 checkedTerminal_1792_64

theorem checkedTerminalPrefix1868 : checkRange checkTerminalAt 0 1868 = true :=
  checkRange_join checkTerminalAt 0 1856 12 checkedTerminalPrefix1856 checkedTerminal_1856_12

theorem terminalWitness_checks (i : Fin 1868) :
    (terminalWitness i).Checks officialRows (layer15 i) := by
  apply checkOrbit_sound
  have h := checkRange_sound checkTerminalAt 0 1868 checkedTerminalPrefix1868 i.val (Nat.zero_le _) i.isLt
  simpa only [checkTerminalAt, dif_pos i.isLt] using h

theorem terminal_covered {K : Type*} [CommRing K] (q : Fin 20 → K)
    (h : Covered q layer15) : InOrbits officialRows q := by
  obtain ⟨i, hi⟩ := h
  exact orbitWitness_sound officialRows q (layer15 i) (terminalWitness i) (terminalWitness_checks i) hi

end Paper2.Certificates.Q6.Coverage
