import Paper2.Certificates.Q6Coverage.Actions02

namespace Paper2.Certificates.Q6.Coverage

def action48 : Action := ⟨![0,3,1,2,4,5],false,![1,4,7,8,0,2,3,5,6,9,10,13,14,16,17,19,11,12,15,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action48_valid : action48.Valid :=
  Action.check_sound _ (by decide +kernel)

def action49 : Action := ⟨![0,3,1,2,5,4],false,![1,4,8,7,0,3,2,6,5,9,10,14,13,17,16,19,12,11,15,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action49_valid : action49.Valid :=
  Action.check_sound _ (by decide +kernel)

def action50 : Action := ⟨![0,3,1,4,2,5],false,![1,7,4,8,2,0,3,5,9,6,13,10,14,16,19,17,11,15,12,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action50_valid : action50.Valid :=
  Action.check_sound _ (by decide +kernel)

def action51 : Action := ⟨![0,3,1,4,5,2],false,![1,7,8,4,2,3,0,9,5,6,13,14,10,19,16,17,15,11,12,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action51_valid : action51.Valid :=
  Action.check_sound _ (by decide +kernel)

def action52 : Action := ⟨![0,3,1,5,2,4],false,![1,8,4,7,3,0,2,6,9,5,14,10,13,17,19,16,12,15,11,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action52_valid : action52.Valid :=
  Action.check_sound _ (by decide +kernel)

def action53 : Action := ⟨![0,3,1,5,4,2],false,![1,8,7,4,3,2,0,9,6,5,14,13,10,19,17,16,15,12,11,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action53_valid : action53.Valid :=
  Action.check_sound _ (by decide +kernel)

def action54 : Action := ⟨![0,3,2,1,4,5],false,![4,1,7,8,0,5,6,2,3,9,10,16,17,13,14,19,11,12,18,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action54_valid : action54.Valid :=
  Action.check_sound _ (by decide +kernel)

def action55 : Action := ⟨![0,3,2,1,5,4],false,![4,1,8,7,0,6,5,3,2,9,10,17,16,14,13,19,12,11,18,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action55_valid : action55.Valid :=
  Action.check_sound _ (by decide +kernel)

def action56 : Action := ⟨![0,3,2,4,1,5],false,![4,7,1,8,5,0,6,2,9,3,16,10,17,13,19,14,11,18,12,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action56_valid : action56.Valid :=
  Action.check_sound _ (by decide +kernel)

def action57 : Action := ⟨![0,3,2,4,5,1],false,![4,7,8,1,5,6,0,9,2,3,16,17,10,19,13,14,18,11,12,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action57_valid : action57.Valid :=
  Action.check_sound _ (by decide +kernel)

def action58 : Action := ⟨![0,3,2,5,1,4],false,![4,8,1,7,6,0,5,3,9,2,17,10,16,14,19,13,12,18,11,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action58_valid : action58.Valid :=
  Action.check_sound _ (by decide +kernel)

def action59 : Action := ⟨![0,3,2,5,4,1],false,![4,8,7,1,6,5,0,9,3,2,17,16,10,19,14,13,18,12,11,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action59_valid : action59.Valid :=
  Action.check_sound _ (by decide +kernel)

def action60 : Action := ⟨![0,3,4,1,2,5],false,![7,1,4,8,2,5,9,0,3,6,13,16,19,10,14,17,11,15,18,12]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action60_valid : action60.Valid :=
  Action.check_sound _ (by decide +kernel)

def action61 : Action := ⟨![0,3,4,1,5,2],false,![7,1,8,4,2,9,5,3,0,6,13,19,16,14,10,17,15,11,18,12]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action61_valid : action61.Valid :=
  Action.check_sound _ (by decide +kernel)

def action62 : Action := ⟨![0,3,4,2,1,5],false,![7,4,1,8,5,2,9,0,6,3,16,13,19,10,17,14,11,18,15,12]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action62_valid : action62.Valid :=
  Action.check_sound _ (by decide +kernel)

def action63 : Action := ⟨![0,3,4,2,5,1],false,![7,4,8,1,5,9,2,6,0,3,16,19,13,17,10,14,18,11,15,12]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action63_valid : action63.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
