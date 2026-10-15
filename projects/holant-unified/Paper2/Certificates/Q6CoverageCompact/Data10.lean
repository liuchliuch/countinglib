import Paper2.Certificates.Q6CoverageCompact.Layer10Part043

namespace Paper2.Certificates.Q6.Coverage

theorem checked10 : checkTransition layer9 layer10 next10 (loopOptions 9) = true := checked10_0_4033

theorem transition10 (i : Fin 4033) (b : Fin 3) :
    refine (layer9 i) (loopOptions 9 b) = layer10 (next10 i b) :=
  checkTransition_sound _ _ _ _ checked10 i b

end Paper2.Certificates.Q6.Coverage
