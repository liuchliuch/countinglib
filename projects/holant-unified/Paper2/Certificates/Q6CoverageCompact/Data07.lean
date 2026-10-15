import Paper2.Certificates.Q6CoverageCompact.Layer07Part013

namespace Paper2.Certificates.Q6.Coverage

theorem checked7 : checkTransition layer6 layer7 next7 (loopOptions 6) = true := checked7_0_729

theorem transition7 (i : Fin 729) (b : Fin 3) :
    refine (layer6 i) (loopOptions 6 b) = layer7 (next7 i b) :=
  checkTransition_sound _ _ _ _ checked7 i b

end Paper2.Certificates.Q6.Coverage
