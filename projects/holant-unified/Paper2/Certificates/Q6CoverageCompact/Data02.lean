import Paper2.Certificates.Q6CoverageCompact.Layer02Part001

namespace Paper2.Certificates.Q6.Coverage

theorem checked2 : checkTransition layer1 layer2 next2 (loopOptions 1) = true := checked2_0_3

theorem transition2 (i : Fin 3) (b : Fin 3) :
    refine (layer1 i) (loopOptions 1 b) = layer2 (next2 i b) :=
  checkTransition_sound _ _ _ _ checked2 i b

end Paper2.Certificates.Q6.Coverage
