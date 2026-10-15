import Paper2.Certificates.Q6CoverageCompact.Layer13Part039

namespace Paper2.Certificates.Q6.Coverage

theorem checked13 : checkTransition layer12 layer13 next13 (loopOptions 12) = true := checked13_0_2396

theorem transition13 (i : Fin 2396) (b : Fin 3) :
    refine (layer12 i) (loopOptions 12 b) = layer13 (next13 i b) :=
  checkTransition_sound _ _ _ _ checked13 i b

end Paper2.Certificates.Q6.Coverage
