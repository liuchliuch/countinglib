import Paper2.Certificates.Q6CoverageCompact.Layer12Part040

namespace Paper2.Certificates.Q6.Coverage

theorem checked12 : checkTransition layer11 layer12 next12 (loopOptions 11) = true := checked12_0_3109

theorem transition12 (i : Fin 3109) (b : Fin 3) :
    refine (layer11 i) (loopOptions 11 b) = layer12 (next12 i b) :=
  checkTransition_sound _ _ _ _ checked12 i b

end Paper2.Certificates.Q6.Coverage
