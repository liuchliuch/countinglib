import Paper2.Certificates.Q6Coverage.Actions18

namespace Paper2.Certificates.Q6.Coverage

def action304 : Action := ⟨![2,5,1,3,4,0],false,![12,17,18,6,10,11,0,16,4,5,14,15,3,19,8,9,13,1,2,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action304_valid : action304.Valid :=
  Action.check_sound _ (by decide +kernel)

def action305 : Action := ⟨![2,5,1,4,0,3],false,![12,18,6,17,11,0,10,5,16,4,15,3,14,9,19,8,2,13,1,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action305_valid : action305.Valid :=
  Action.check_sound _ (by decide +kernel)

def action306 : Action := ⟨![2,5,1,4,3,0],false,![12,18,17,6,11,10,0,16,5,4,15,14,3,19,9,8,13,2,1,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action306_valid : action306.Valid :=
  Action.check_sound _ (by decide +kernel)

def action307 : Action := ⟨![2,5,3,0,4,1],false,![17,6,18,12,4,16,10,5,0,11,8,19,14,9,3,15,7,1,13,2]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action307_valid : action307.Valid :=
  Action.check_sound _ (by decide +kernel)

def action308 : Action := ⟨![2,5,3,1,4,0],false,![17,12,18,6,10,16,4,11,0,5,14,19,8,15,3,9,13,1,7,2]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action308_valid : action308.Valid :=
  Action.check_sound _ (by decide +kernel)

def action309 : Action := ⟨![2,5,3,4,0,1],false,![17,18,6,12,16,4,10,5,11,0,19,8,14,9,15,3,7,13,1,2]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action309_valid : action309.Valid :=
  Action.check_sound _ (by decide +kernel)

def action310 : Action := ⟨![2,5,3,4,1,0],false,![17,18,12,6,16,10,4,11,5,0,19,14,8,15,9,3,13,7,1,2]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action310_valid : action310.Valid :=
  Action.check_sound _ (by decide +kernel)

def action311 : Action := ⟨![2,5,4,0,3,1],false,![18,6,17,12,5,16,11,4,0,10,9,19,15,8,3,14,7,2,13,1]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action311_valid : action311.Valid :=
  Action.check_sound _ (by decide +kernel)

def action312 : Action := ⟨![2,5,4,1,3,0],false,![18,12,17,6,11,16,5,10,0,4,15,19,9,14,3,8,13,2,7,1]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action312_valid : action312.Valid :=
  Action.check_sound _ (by decide +kernel)

def action313 : Action := ⟨![2,5,4,3,0,1],false,![18,17,6,12,16,5,11,4,10,0,19,9,15,8,14,3,7,13,2,1]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action313_valid : action313.Valid :=
  Action.check_sound _ (by decide +kernel)

def action314 : Action := ⟨![3,4,0,1,2,5],false,![7,13,16,19,1,4,8,10,14,17,2,5,9,11,15,18,0,3,6,12]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action314_valid : action314.Valid :=
  Action.check_sound _ (by decide +kernel)

def action315 : Action := ⟨![3,4,0,1,5,2],false,![7,13,19,16,1,8,4,14,10,17,2,9,5,15,11,18,3,0,6,12]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action315_valid : action315.Valid :=
  Action.check_sound _ (by decide +kernel)

def action316 : Action := ⟨![3,4,0,2,1,5],false,![7,16,13,19,4,1,8,10,17,14,5,2,9,11,18,15,0,6,3,12]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action316_valid : action316.Valid :=
  Action.check_sound _ (by decide +kernel)

def action317 : Action := ⟨![3,4,0,2,5,1],false,![7,16,19,13,4,8,1,17,10,14,5,9,2,18,11,15,6,0,3,12]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action317_valid : action317.Valid :=
  Action.check_sound _ (by decide +kernel)

def action318 : Action := ⟨![3,4,0,5,1,2],false,![7,19,13,16,8,1,4,14,17,10,9,2,5,15,18,11,3,6,0,12]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action318_valid : action318.Valid :=
  Action.check_sound _ (by decide +kernel)

def action319 : Action := ⟨![3,4,0,5,2,1],false,![7,19,16,13,8,4,1,17,14,10,9,5,2,18,15,11,6,3,0,12]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action319_valid : action319.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
