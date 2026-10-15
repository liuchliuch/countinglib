import Paper2.Certificates.Q6Coverage.Actions01

namespace Paper2.Certificates.Q6.Coverage

def action32 : Action := ⟨![0,2,3,4,1,5],false,![4,5,0,6,7,1,8,2,9,3,16,10,17,11,18,12,13,19,14,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action32_valid : action32.Valid :=
  Action.check_sound _ (by decide +kernel)

def action33 : Action := ⟨![0,2,3,4,5,1],false,![4,5,6,0,7,8,1,9,2,3,16,17,10,18,11,12,19,13,14,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action33_valid : action33.Valid :=
  Action.check_sound _ (by decide +kernel)

def action34 : Action := ⟨![0,2,3,5,1,4],false,![4,6,0,5,8,1,7,3,9,2,17,10,16,12,18,11,14,19,13,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action34_valid : action34.Valid :=
  Action.check_sound _ (by decide +kernel)

def action35 : Action := ⟨![0,2,3,5,4,1],false,![4,6,5,0,8,7,1,9,3,2,17,16,10,18,12,11,19,14,13,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action35_valid : action35.Valid :=
  Action.check_sound _ (by decide +kernel)

def action36 : Action := ⟨![0,2,4,1,3,5],false,![5,0,4,6,2,7,9,1,3,8,11,16,18,10,12,17,13,15,19,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action36_valid : action36.Valid :=
  Action.check_sound _ (by decide +kernel)

def action37 : Action := ⟨![0,2,4,1,5,3],false,![5,0,6,4,2,9,7,3,1,8,11,18,16,12,10,17,15,13,19,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action37_valid : action37.Valid :=
  Action.check_sound _ (by decide +kernel)

def action38 : Action := ⟨![0,2,4,3,1,5],false,![5,4,0,6,7,2,9,1,8,3,16,11,18,10,17,12,13,19,15,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action38_valid : action38.Valid :=
  Action.check_sound _ (by decide +kernel)

def action39 : Action := ⟨![0,2,4,3,5,1],false,![5,4,6,0,7,9,2,8,1,3,16,18,11,17,10,12,19,13,15,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action39_valid : action39.Valid :=
  Action.check_sound _ (by decide +kernel)

def action40 : Action := ⟨![0,2,4,5,1,3],false,![5,6,0,4,9,2,7,3,8,1,18,11,16,12,17,10,15,19,13,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action40_valid : action40.Valid :=
  Action.check_sound _ (by decide +kernel)

def action41 : Action := ⟨![0,2,4,5,3,1],false,![5,6,4,0,9,7,2,8,3,1,18,16,11,17,12,10,19,15,13,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action41_valid : action41.Valid :=
  Action.check_sound _ (by decide +kernel)

def action42 : Action := ⟨![0,2,5,1,3,4],false,![6,0,4,5,3,8,9,1,2,7,12,17,18,10,11,16,14,15,19,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action42_valid : action42.Valid :=
  Action.check_sound _ (by decide +kernel)

def action43 : Action := ⟨![0,2,5,1,4,3],false,![6,0,5,4,3,9,8,2,1,7,12,18,17,11,10,16,15,14,19,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action43_valid : action43.Valid :=
  Action.check_sound _ (by decide +kernel)

def action44 : Action := ⟨![0,2,5,3,1,4],false,![6,4,0,5,8,3,9,1,7,2,17,12,18,10,16,11,14,19,15,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action44_valid : action44.Valid :=
  Action.check_sound _ (by decide +kernel)

def action45 : Action := ⟨![0,2,5,3,4,1],false,![6,4,5,0,8,9,3,7,1,2,17,18,12,16,10,11,19,14,15,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action45_valid : action45.Valid :=
  Action.check_sound _ (by decide +kernel)

def action46 : Action := ⟨![0,2,5,4,1,3],false,![6,5,0,4,9,3,8,2,7,1,18,12,17,11,16,10,15,19,14,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action46_valid : action46.Valid :=
  Action.check_sound _ (by decide +kernel)

def action47 : Action := ⟨![0,2,5,4,3,1],false,![6,5,4,0,9,8,3,7,2,1,18,17,12,16,11,10,19,15,14,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action47_valid : action47.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
