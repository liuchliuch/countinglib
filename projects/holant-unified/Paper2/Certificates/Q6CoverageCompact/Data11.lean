import Paper2.Certificates.Q6CoverageCompact.Layer11Part042

namespace Paper2.Certificates.Q6.Coverage

theorem checked11 : checkTransition layer10 layer11 next11 (loopOptions 10) = true := checked11_0_3959

theorem transition11 (i : Fin 3959) (b : Fin 3) :
    refine (layer10 i) (loopOptions 10 b) = layer11 (next11 i b) :=
  checkTransition_sound _ _ _ _ checked11 i b

end Paper2.Certificates.Q6.Coverage
