import Paper2.Certificates.Q6Coverage.Actions15

namespace Paper2.Certificates.Q6.Coverage

def action256 : Action := ⟨![2,3,0,5,1,4],false,![4,17,10,16,6,0,5,12,18,11,8,1,7,14,19,13,3,9,2,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action256_valid : action256.Valid :=
  Action.check_sound _ (by decide +kernel)

def action257 : Action := ⟨![2,3,0,5,4,1],false,![4,17,16,10,6,5,0,18,12,11,8,7,1,19,14,13,9,3,2,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action257_valid : action257.Valid :=
  Action.check_sound _ (by decide +kernel)

def action258 : Action := ⟨![2,3,1,0,4,5],false,![10,4,16,17,0,11,12,5,6,18,1,13,14,7,8,19,2,3,15,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action258_valid : action258.Valid :=
  Action.check_sound _ (by decide +kernel)

def action259 : Action := ⟨![2,3,1,0,5,4],false,![10,4,17,16,0,12,11,6,5,18,1,14,13,8,7,19,3,2,15,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action259_valid : action259.Valid :=
  Action.check_sound _ (by decide +kernel)

def action260 : Action := ⟨![2,3,1,4,0,5],false,![10,16,4,17,11,0,12,5,18,6,13,1,14,7,19,8,2,15,3,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action260_valid : action260.Valid :=
  Action.check_sound _ (by decide +kernel)

def action261 : Action := ⟨![2,3,1,4,5,0],false,![10,16,17,4,11,12,0,18,5,6,13,14,1,19,7,8,15,2,3,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action261_valid : action261.Valid :=
  Action.check_sound _ (by decide +kernel)

def action262 : Action := ⟨![2,3,1,5,0,4],false,![10,17,4,16,12,0,11,6,18,5,14,1,13,8,19,7,3,15,2,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action262_valid : action262.Valid :=
  Action.check_sound _ (by decide +kernel)

def action263 : Action := ⟨![2,3,1,5,4,0],false,![10,17,16,4,12,11,0,18,6,5,14,13,1,19,8,7,15,3,2,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action263_valid : action263.Valid :=
  Action.check_sound _ (by decide +kernel)

def action264 : Action := ⟨![2,3,4,0,1,5],false,![16,4,10,17,5,11,18,0,6,12,7,13,19,1,8,14,2,9,15,3]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action264_valid : action264.Valid :=
  Action.check_sound _ (by decide +kernel)

def action265 : Action := ⟨![2,3,4,0,5,1],false,![16,4,17,10,5,18,11,6,0,12,7,19,13,8,1,14,9,2,15,3]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action265_valid : action265.Valid :=
  Action.check_sound _ (by decide +kernel)

def action266 : Action := ⟨![2,3,4,1,5,0],false,![16,10,17,4,11,18,5,12,0,6,13,19,7,14,1,8,15,2,9,3]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action266_valid : action266.Valid :=
  Action.check_sound _ (by decide +kernel)

def action267 : Action := ⟨![2,3,4,5,0,1],false,![16,17,4,10,18,5,11,6,12,0,19,7,13,8,14,1,9,15,2,3]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action267_valid : action267.Valid :=
  Action.check_sound _ (by decide +kernel)

def action268 : Action := ⟨![2,3,4,5,1,0],false,![16,17,10,4,18,11,5,12,6,0,19,13,7,14,8,1,15,9,2,3]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action268_valid : action268.Valid :=
  Action.check_sound _ (by decide +kernel)

def action269 : Action := ⟨![2,3,5,0,1,4],false,![17,4,10,16,6,12,18,0,5,11,8,14,19,1,7,13,3,9,15,2]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action269_valid : action269.Valid :=
  Action.check_sound _ (by decide +kernel)

def action270 : Action := ⟨![2,3,5,0,4,1],false,![17,4,16,10,6,18,12,5,0,11,8,19,14,7,1,13,9,3,15,2]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action270_valid : action270.Valid :=
  Action.check_sound _ (by decide +kernel)

def action271 : Action := ⟨![2,3,5,1,4,0],false,![17,10,16,4,12,18,6,11,0,5,14,19,8,13,1,7,15,3,9,2]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action271_valid : action271.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
