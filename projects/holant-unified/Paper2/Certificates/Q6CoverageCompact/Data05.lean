import Paper2.Certificates.Q6CoverageCompact.Layer05Part001

namespace Paper2.Certificates.Q6.Coverage

theorem checked5 : checkTransition layer4 layer5 next5 (loopOptions 4) = true := checked5_0_81

theorem transition5 (i : Fin 81) (b : Fin 3) :
    refine (layer4 i) (loopOptions 4 b) = layer5 (next5 i b) :=
  checkTransition_sound _ _ _ _ checked5 i b

end Paper2.Certificates.Q6.Coverage
