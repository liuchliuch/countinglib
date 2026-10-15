import Paper2.Certificates.Q6CoverageCompact.Layer14Part024

namespace Paper2.Certificates.Q6.Coverage

theorem checked14 : checkTransition layer13 layer14 next14 (loopOptions 13) = true := checked14_0_2085

theorem transition14 (i : Fin 2085) (b : Fin 3) :
    refine (layer13 i) (loopOptions 13 b) = layer14 (next14 i b) :=
  checkTransition_sound _ _ _ _ checked14 i b

end Paper2.Certificates.Q6.Coverage
