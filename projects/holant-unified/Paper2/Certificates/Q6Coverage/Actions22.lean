import Paper2.Certificates.Q6Coverage.Actions21

namespace Paper2.Certificates.Q6.Coverage

def action352 : Action := ⟨![4,5,1,0,2,3],false,![15,9,18,19,2,11,13,5,7,16,3,12,14,6,8,17,0,1,10,4]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action352_valid : action352.Valid :=
  Action.check_sound _ (by decide +kernel)

def action353 : Action := ⟨![4,5,1,0,3,2],false,![15,9,19,18,2,13,11,7,5,16,3,14,12,8,6,17,1,0,10,4]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action353_valid : action353.Valid :=
  Action.check_sound _ (by decide +kernel)

def action354 : Action := ⟨![4,5,1,2,0,3],false,![15,18,9,19,11,2,13,5,16,7,12,3,14,6,17,8,0,10,1,4]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action354_valid : action354.Valid :=
  Action.check_sound _ (by decide +kernel)

def action355 : Action := ⟨![4,5,1,2,3,0],false,![15,18,19,9,11,13,2,16,5,7,12,14,3,17,6,8,10,0,1,4]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action355_valid : action355.Valid :=
  Action.check_sound _ (by decide +kernel)

def action356 : Action := ⟨![4,5,1,3,0,2],false,![15,19,9,18,13,2,11,7,16,5,14,3,12,8,17,6,1,10,0,4]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action356_valid : action356.Valid :=
  Action.check_sound _ (by decide +kernel)

def action357 : Action := ⟨![4,5,1,3,2,0],false,![15,19,18,9,13,11,2,16,7,5,14,12,3,17,8,6,10,1,0,4]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action357_valid : action357.Valid :=
  Action.check_sound _ (by decide +kernel)

def action358 : Action := ⟨![4,5,2,0,3,1],false,![18,9,19,15,5,16,11,7,2,13,6,17,12,8,3,14,4,0,10,1]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action358_valid : action358.Valid :=
  Action.check_sound _ (by decide +kernel)

def action359 : Action := ⟨![4,5,2,1,3,0],false,![18,15,19,9,11,16,5,13,2,7,12,17,6,14,3,8,10,0,4,1]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action359_valid : action359.Valid :=
  Action.check_sound _ (by decide +kernel)

def action360 : Action := ⟨![4,5,2,3,0,1],false,![18,19,9,15,16,5,11,7,13,2,17,6,12,8,14,3,4,10,0,1]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action360_valid : action360.Valid :=
  Action.check_sound _ (by decide +kernel)

def action361 : Action := ⟨![4,5,2,3,1,0],false,![18,19,15,9,16,11,5,13,7,2,17,12,6,14,8,3,10,4,0,1]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action361_valid : action361.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
