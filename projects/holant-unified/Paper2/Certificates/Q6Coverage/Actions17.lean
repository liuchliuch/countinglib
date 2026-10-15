import Paper2.Certificates.Q6Coverage.Actions16

namespace Paper2.Certificates.Q6.Coverage

def action272 : Action := ⟨![2,3,5,4,0,1],false,![17,16,4,10,18,6,12,5,11,0,19,8,14,7,13,1,9,15,3,2]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action272_valid : action272.Valid :=
  Action.check_sound _ (by decide +kernel)

def action273 : Action := ⟨![2,3,5,4,1,0],false,![17,16,10,4,18,12,6,11,5,0,19,14,8,13,7,1,15,9,3,2]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action273_valid : action273.Valid :=
  Action.check_sound _ (by decide +kernel)

def action274 : Action := ⟨![2,4,0,1,3,5],false,![5,11,16,18,0,4,6,10,12,17,2,7,9,13,15,19,1,3,8,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action274_valid : action274.Valid :=
  Action.check_sound _ (by decide +kernel)

def action275 : Action := ⟨![2,4,0,1,5,3],false,![5,11,18,16,0,6,4,12,10,17,2,9,7,15,13,19,3,1,8,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action275_valid : action275.Valid :=
  Action.check_sound _ (by decide +kernel)

def action276 : Action := ⟨![2,4,0,3,1,5],false,![5,16,11,18,4,0,6,10,17,12,7,2,9,13,19,15,1,8,3,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action276_valid : action276.Valid :=
  Action.check_sound _ (by decide +kernel)

def action277 : Action := ⟨![2,4,0,3,5,1],false,![5,16,18,11,4,6,0,17,10,12,7,9,2,19,13,15,8,1,3,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action277_valid : action277.Valid :=
  Action.check_sound _ (by decide +kernel)

def action278 : Action := ⟨![2,4,0,5,1,3],false,![5,18,11,16,6,0,4,12,17,10,9,2,7,15,19,13,3,8,1,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action278_valid : action278.Valid :=
  Action.check_sound _ (by decide +kernel)

def action279 : Action := ⟨![2,4,0,5,3,1],false,![5,18,16,11,6,4,0,17,12,10,9,7,2,19,15,13,8,3,1,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action279_valid : action279.Valid :=
  Action.check_sound _ (by decide +kernel)

def action280 : Action := ⟨![2,4,1,0,3,5],false,![11,5,16,18,0,10,12,4,6,17,2,13,15,7,9,19,1,3,14,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action280_valid : action280.Valid :=
  Action.check_sound _ (by decide +kernel)

def action281 : Action := ⟨![2,4,1,0,5,3],false,![11,5,18,16,0,12,10,6,4,17,2,15,13,9,7,19,3,1,14,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action281_valid : action281.Valid :=
  Action.check_sound _ (by decide +kernel)

def action282 : Action := ⟨![2,4,1,3,0,5],false,![11,16,5,18,10,0,12,4,17,6,13,2,15,7,19,9,1,14,3,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action282_valid : action282.Valid :=
  Action.check_sound _ (by decide +kernel)

def action283 : Action := ⟨![2,4,1,3,5,0],false,![11,16,18,5,10,12,0,17,4,6,13,15,2,19,7,9,14,1,3,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action283_valid : action283.Valid :=
  Action.check_sound _ (by decide +kernel)

def action284 : Action := ⟨![2,4,1,5,0,3],false,![11,18,5,16,12,0,10,6,17,4,15,2,13,9,19,7,3,14,1,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action284_valid : action284.Valid :=
  Action.check_sound _ (by decide +kernel)

def action285 : Action := ⟨![2,4,1,5,3,0],false,![11,18,16,5,12,10,0,17,6,4,15,13,2,19,9,7,14,3,1,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action285_valid : action285.Valid :=
  Action.check_sound _ (by decide +kernel)

def action286 : Action := ⟨![2,4,3,0,5,1],false,![16,5,18,11,4,17,10,6,0,12,7,19,13,9,2,15,8,1,14,3]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action286_valid : action286.Valid :=
  Action.check_sound _ (by decide +kernel)

def action287 : Action := ⟨![2,4,3,1,5,0],false,![16,11,18,5,10,17,4,12,0,6,13,19,7,15,2,9,14,1,8,3]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action287_valid : action287.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
