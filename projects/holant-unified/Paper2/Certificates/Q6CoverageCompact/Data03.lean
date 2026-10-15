import Paper2.Certificates.Q6CoverageCompact.Layer03Part001

namespace Paper2.Certificates.Q6.Coverage

theorem checked3 : checkTransition layer2 layer3 next3 (loopOptions 2) = true := checked3_0_9

theorem transition3 (i : Fin 9) (b : Fin 3) :
    refine (layer2 i) (loopOptions 2 b) = layer3 (next3 i b) :=
  checkTransition_sound _ _ _ _ checked3 i b

end Paper2.Certificates.Q6.Coverage
