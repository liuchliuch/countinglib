import Paper2.Certificates.Q6CoverageCompact.Layer09Part043

namespace Paper2.Certificates.Q6.Coverage

theorem checked9 : checkTransition layer8 layer9 next9 (loopOptions 8) = true := checked9_0_3321

theorem transition9 (i : Fin 3321) (b : Fin 3) :
    refine (layer8 i) (loopOptions 8 b) = layer9 (next9 i b) :=
  checkTransition_sound _ _ _ _ checked9 i b

end Paper2.Certificates.Q6.Coverage
