import Paper2.Certificates.Q6CoverageCompact.Layer15Part021

namespace Paper2.Certificates.Q6.Coverage

theorem checked15 : checkTransition layer14 layer15 next15 (loopOptions 14) = true := checked15_0_1937

theorem transition15 (i : Fin 1937) (b : Fin 3) :
    refine (layer14 i) (loopOptions 14 b) = layer15 (next15 i b) :=
  checkTransition_sound _ _ _ _ checked15 i b

end Paper2.Certificates.Q6.Coverage
