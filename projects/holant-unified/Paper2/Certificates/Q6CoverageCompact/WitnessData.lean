import Paper2.Certificates.Q6CoverageCompact.WitnessPart004

namespace Paper2.Certificates.Q6.Coverage

def terminalWitness (i : Fin 1868) : OrbitWitness := witnessTree i.val

def checkTerminalAt (i : Nat) : Bool :=
  if hi : i < 1868 then checkOrbit officialRows (layer15 ⟨i,hi⟩) (terminalWitness ⟨i,hi⟩) else true

end Paper2.Certificates.Q6.Coverage
