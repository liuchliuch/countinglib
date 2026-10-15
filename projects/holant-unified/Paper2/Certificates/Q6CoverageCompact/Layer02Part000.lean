import Paper2.Certificates.Q6CoverageCompact.Data01

namespace Paper2.Certificates.Q6.Coverage

def state2_0 : State := natState 404113103371204058887482836299554880

def state2_1 : State := natState 400599175907372222102037732105396288

def state2_2 : State := natState 400544270790800971290657729024892992

def state2_3 : State := natState 404113086310843925503504050631221312

def state2_4 : State := natState 400599158847011039559489750934757440

def state2_5 : State := natState 400544253730440821765777878810370112

def state2_6 : State := natState 404113086044340862391570364906610752

def state2_7 : State := natState 400599158580509009465224196166262848

def state2_8 : State := natState 400544253463871645523083811894337600

def stree2L (i : Nat) : State := match i with | 0 => state2_0 | 1 => state2_1 | 2 => state2_2 | _ => state2_3

def stree2R (i : Nat) : State := match i with | 0 => state2_4 | 1 => state2_5 | 2 => state2_6 | 3 => state2_7 | _ => state2_8

def stree2 (i : Nat) : State := if i < 4 then stree2L i else stree2R (i - 4)

def ntree2 (i : Nat) : Fin 3 → Fin 9 := match i with | 0 => ![⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨3,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩] | _ => ![⟨6,by decide⟩,⟨7,by decide⟩,⟨8,by decide⟩]

def layer2 : Fin 9 → State := fun i => stree2 i.val

def next2 : Fin 3 → Fin 3 → Fin 9 := fun i => ntree2 i.val

end Paper2.Certificates.Q6.Coverage
