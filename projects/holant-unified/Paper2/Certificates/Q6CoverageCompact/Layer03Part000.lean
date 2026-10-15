import Paper2.Certificates.Q6CoverageCompact.Data02

namespace Paper2.Certificates.Q6.Coverage

def state3_0 : State := natState 611804977712597162875781184844734464

def state3_1 : State := natState 404158738795532358240069633258037312

def state3_2 : State := natState 404113816598752005291027779352797248

def state3_3 : State := natState 608291050248765322631571566779703360

def state3_4 : State := natState 400589034705290479360395724169420864

def state3_5 : State := natState 400599889134920168505582675158638656

def state3_6 : State := natState 608236145132194071820191563699200064

def state3_7 : State := natState 400589906215129270643244525983375424

def state3_8 : State := natState 400544112508561260786480347001659456

def state3_9 : State := natState 611804960652237029491802399193178112

def state3_10 : State := natState 404158721735172224856090847589703744

def state3_11 : State := natState 404113799267592488311964683666726976

def state3_12 : State := natState 608291033188404156229924650172031040

def state3_13 : State := natState 400589017606243670590179609408184384

def state3_14 : State := natState 400574281107267494986907669274304576

def state3_15 : State := natState 608236128071833938436212778047643712

def state3_16 : State := natState 400589889154769121118364675768852544

def state3_17 : State := natState 400544095177401727666516186769399872

def state3_18 : State := natState 611804960385733966379868713468567552

def state3_19 : State := natState 404158721464437921375483969521066048

def state3_20 : State := natState 404113799271888808795115307959853120

def state3_21 : State := natState 608291032921902126135659095403536448

def state3_22 : State := natState 400589017374196026354908995886260288

def state3_23 : State := natState 400599871808056955868769139219505216

def state3_24 : State := natState 608236127805264762193518711131611200

def state3_25 : State := natState 400574280935953394432491488350576704

def state3_26 : State := natState 400544095181027472109099115283750976

def stree3LL (i : Nat) : State := match i with | 0 => state3_0 | 1 => state3_1 | 2 => state3_2 | 3 => state3_3 | 4 => state3_4 | _ => state3_5

def stree3LR (i : Nat) : State := match i with | 0 => state3_6 | 1 => state3_7 | 2 => state3_8 | 3 => state3_9 | 4 => state3_10 | 5 => state3_11 | _ => state3_12

def stree3L (i : Nat) : State := if i < 6 then stree3LL i else stree3LR (i - 6)

def stree3RL (i : Nat) : State := match i with | 0 => state3_13 | 1 => state3_14 | 2 => state3_15 | 3 => state3_16 | 4 => state3_17 | 5 => state3_18 | _ => state3_19

def stree3RR (i : Nat) : State := match i with | 0 => state3_20 | 1 => state3_21 | 2 => state3_22 | 3 => state3_23 | 4 => state3_24 | 5 => state3_25 | _ => state3_26

def stree3R (i : Nat) : State := if i < 7 then stree3RL i else stree3RR (i - 7)

def stree3 (i : Nat) : State := if i < 13 then stree3L i else stree3R (i - 13)

def ntree3L (i : Nat) : Fin 3 → Fin 27 := match i with | 0 => ![⟨0,by decide⟩,⟨1,by decide⟩,⟨2,by decide⟩] | 1 => ![⟨3,by decide⟩,⟨4,by decide⟩,⟨5,by decide⟩] | 2 => ![⟨6,by decide⟩,⟨7,by decide⟩,⟨8,by decide⟩] | _ => ![⟨9,by decide⟩,⟨10,by decide⟩,⟨11,by decide⟩]

def ntree3R (i : Nat) : Fin 3 → Fin 27 := match i with | 0 => ![⟨12,by decide⟩,⟨13,by decide⟩,⟨14,by decide⟩] | 1 => ![⟨15,by decide⟩,⟨16,by decide⟩,⟨17,by decide⟩] | 2 => ![⟨18,by decide⟩,⟨19,by decide⟩,⟨20,by decide⟩] | 3 => ![⟨21,by decide⟩,⟨22,by decide⟩,⟨23,by decide⟩] | _ => ![⟨24,by decide⟩,⟨25,by decide⟩,⟨26,by decide⟩]

def ntree3 (i : Nat) : Fin 3 → Fin 27 := if i < 4 then ntree3L i else ntree3R (i - 4)

def layer3 : Fin 27 → State := fun i => stree3 i.val

def next3 : Fin 9 → Fin 3 → Fin 27 := fun i => ntree3 i.val

end Paper2.Certificates.Q6.Coverage
