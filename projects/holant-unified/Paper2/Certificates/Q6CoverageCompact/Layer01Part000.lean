import Paper2.Certificates.Q6Coverage.Data00
import Paper2.Certificates.Q6Coverage.NatCore

namespace Paper2.Certificates.Q6.Coverage

def state1_0 : State := natState 400543399280961368351632633944088640

def state1_1 : State := natState 400543382220601218826752783729565760

def state1_2 : State := natState 400543381954098155714819098004955200

def stree1 (i : Nat) : State := match i with | 0 => state1_0 | 1 => state1_1 | _ => state1_2

def ntree1 (i : Nat) : Fin 3 → Fin 3 := match i with  | _ => ![⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩]

def layer1 : Fin 3 → State := fun i => stree1 i.val

def next1 : Fin 1 → Fin 3 → Fin 3 := fun i => ntree1 i.val

end Paper2.Certificates.Q6.Coverage
