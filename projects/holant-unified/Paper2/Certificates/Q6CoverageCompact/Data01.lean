import Paper2.Certificates.Q6CoverageCompact.Layer01Part001

namespace Paper2.Certificates.Q6.Coverage

theorem checked1 : checkTransition layer0 layer1 next1 (loopOptions 0) = true := checked1_0_1

theorem transition1 (i : Fin 1) (b : Fin 3) :
    refine (layer0 i) (loopOptions 0 b) = layer1 (next1 i b) :=
  checkTransition_sound _ _ _ _ checked1 i b

end Paper2.Certificates.Q6.Coverage
