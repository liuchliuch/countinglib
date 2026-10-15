import Paper2.Certificates.Q6CoverageCompact.Layer06Part004

namespace Paper2.Certificates.Q6.Coverage

theorem checked6 : checkTransition layer5 layer6 next6 (loopOptions 5) = true := checked6_0_243

theorem transition6 (i : Fin 243) (b : Fin 3) :
    refine (layer5 i) (loopOptions 5 b) = layer6 (next6 i b) :=
  checkTransition_sound _ _ _ _ checked6 i b

end Paper2.Certificates.Q6.Coverage
