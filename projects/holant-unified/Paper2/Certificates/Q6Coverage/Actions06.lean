import Paper2.Certificates.Q6Coverage.Actions05

namespace Paper2.Certificates.Q6.Coverage

def action96 : Action := ⟨![0,5,1,2,3,4],false,![3,6,8,9,0,1,2,4,5,7,12,14,15,17,18,19,10,11,13,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action96_valid : action96.Valid :=
  Action.check_sound _ (by decide +kernel)

def action97 : Action := ⟨![0,5,1,2,4,3],false,![3,6,9,8,0,2,1,5,4,7,12,15,14,18,17,19,11,10,13,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action97_valid : action97.Valid :=
  Action.check_sound _ (by decide +kernel)

def action98 : Action := ⟨![0,5,1,3,2,4],false,![3,8,6,9,1,0,2,4,7,5,14,12,15,17,19,18,10,13,11,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action98_valid : action98.Valid :=
  Action.check_sound _ (by decide +kernel)

def action99 : Action := ⟨![0,5,1,3,4,2],false,![3,8,9,6,1,2,0,7,4,5,14,15,12,19,17,18,13,10,11,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action99_valid : action99.Valid :=
  Action.check_sound _ (by decide +kernel)

def action100 : Action := ⟨![0,5,1,4,2,3],false,![3,9,6,8,2,0,1,5,7,4,15,12,14,18,19,17,11,13,10,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action100_valid : action100.Valid :=
  Action.check_sound _ (by decide +kernel)

def action101 : Action := ⟨![0,5,1,4,3,2],false,![3,9,8,6,2,1,0,7,5,4,15,14,12,19,18,17,13,11,10,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action101_valid : action101.Valid :=
  Action.check_sound _ (by decide +kernel)

def action102 : Action := ⟨![0,5,2,1,3,4],false,![6,3,8,9,0,4,5,1,2,7,12,17,18,14,15,19,10,11,16,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action102_valid : action102.Valid :=
  Action.check_sound _ (by decide +kernel)

def action103 : Action := ⟨![0,5,2,1,4,3],false,![6,3,9,8,0,5,4,2,1,7,12,18,17,15,14,19,11,10,16,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action103_valid : action103.Valid :=
  Action.check_sound _ (by decide +kernel)

def action104 : Action := ⟨![0,5,2,3,1,4],false,![6,8,3,9,4,0,5,1,7,2,17,12,18,14,19,15,10,16,11,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action104_valid : action104.Valid :=
  Action.check_sound _ (by decide +kernel)

def action105 : Action := ⟨![0,5,2,3,4,1],false,![6,8,9,3,4,5,0,7,1,2,17,18,12,19,14,15,16,10,11,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action105_valid : action105.Valid :=
  Action.check_sound _ (by decide +kernel)

def action106 : Action := ⟨![0,5,2,4,1,3],false,![6,9,3,8,5,0,4,2,7,1,18,12,17,15,19,14,11,16,10,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action106_valid : action106.Valid :=
  Action.check_sound _ (by decide +kernel)

def action107 : Action := ⟨![0,5,2,4,3,1],false,![6,9,8,3,5,4,0,7,2,1,18,17,12,19,15,14,16,11,10,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action107_valid : action107.Valid :=
  Action.check_sound _ (by decide +kernel)

def action108 : Action := ⟨![0,5,3,1,2,4],false,![8,3,6,9,1,4,7,0,2,5,14,17,19,12,15,18,10,13,16,11]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action108_valid : action108.Valid :=
  Action.check_sound _ (by decide +kernel)

def action109 : Action := ⟨![0,5,3,1,4,2],false,![8,3,9,6,1,7,4,2,0,5,14,19,17,15,12,18,13,10,16,11]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action109_valid : action109.Valid :=
  Action.check_sound _ (by decide +kernel)

def action110 : Action := ⟨![0,5,3,2,1,4],false,![8,6,3,9,4,1,7,0,5,2,17,14,19,12,18,15,10,16,13,11]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action110_valid : action110.Valid :=
  Action.check_sound _ (by decide +kernel)

def action111 : Action := ⟨![0,5,3,2,4,1],false,![8,6,9,3,4,7,1,5,0,2,17,19,14,18,12,15,16,10,13,11]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action111_valid : action111.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
