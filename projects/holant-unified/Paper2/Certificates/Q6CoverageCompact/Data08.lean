import Paper2.Certificates.Q6CoverageCompact.Layer08Part025

namespace Paper2.Certificates.Q6.Coverage

theorem checked8 : checkTransition layer7 layer8 next8 (loopOptions 7) = true := checked8_0_1812

theorem transition8 (i : Fin 1812) (b : Fin 3) :
    refine (layer7 i) (loopOptions 7 b) = layer8 (next8 i b) :=
  checkTransition_sound _ _ _ _ checked8 i b

end Paper2.Certificates.Q6.Coverage
