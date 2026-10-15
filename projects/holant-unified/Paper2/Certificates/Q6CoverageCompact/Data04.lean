import Paper2.Certificates.Q6CoverageCompact.Layer04Part001

namespace Paper2.Certificates.Q6.Coverage

theorem checked4 : checkTransition layer3 layer4 next4 (loopOptions 3) = true := checked4_0_27

theorem transition4 (i : Fin 27) (b : Fin 3) :
    refine (layer3 i) (loopOptions 3 b) = layer4 (next4 i b) :=
  checkTransition_sound _ _ _ _ checked4 i b

end Paper2.Certificates.Q6.Coverage
