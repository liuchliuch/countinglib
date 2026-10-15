import Paper2.Certificates.Q6Coverage.Actions03

namespace Paper2.Certificates.Q6.Coverage

def action64 : Action := ⟨![0,3,4,5,1,2],false,![7,8,1,4,9,2,5,3,6,0,19,13,16,14,17,10,15,18,11,12]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action64_valid : action64.Valid :=
  Action.check_sound _ (by decide +kernel)

def action65 : Action := ⟨![0,3,4,5,2,1],false,![7,8,4,1,9,5,2,6,3,0,19,16,13,17,14,10,18,15,11,12]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action65_valid : action65.Valid :=
  Action.check_sound _ (by decide +kernel)

def action66 : Action := ⟨![0,3,5,1,2,4],false,![8,1,4,7,3,6,9,0,2,5,14,17,19,10,13,16,12,15,18,11]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action66_valid : action66.Valid :=
  Action.check_sound _ (by decide +kernel)

def action67 : Action := ⟨![0,3,5,1,4,2],false,![8,1,7,4,3,9,6,2,0,5,14,19,17,13,10,16,15,12,18,11]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action67_valid : action67.Valid :=
  Action.check_sound _ (by decide +kernel)

def action68 : Action := ⟨![0,3,5,2,1,4],false,![8,4,1,7,6,3,9,0,5,2,17,14,19,10,16,13,12,18,15,11]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action68_valid : action68.Valid :=
  Action.check_sound _ (by decide +kernel)

def action69 : Action := ⟨![0,3,5,2,4,1],false,![8,4,7,1,6,9,3,5,0,2,17,19,14,16,10,13,18,12,15,11]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action69_valid : action69.Valid :=
  Action.check_sound _ (by decide +kernel)

def action70 : Action := ⟨![0,3,5,4,1,2],false,![8,7,1,4,9,3,6,2,5,0,19,14,17,13,16,10,15,18,12,11]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action70_valid : action70.Valid :=
  Action.check_sound _ (by decide +kernel)

def action71 : Action := ⟨![0,3,5,4,2,1],false,![8,7,4,1,9,6,3,5,2,0,19,17,14,16,13,10,18,15,12,11]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action71_valid : action71.Valid :=
  Action.check_sound _ (by decide +kernel)

def action72 : Action := ⟨![0,4,1,2,3,5],false,![2,5,7,9,0,1,3,4,6,8,11,13,15,16,18,19,10,12,14,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action72_valid : action72.Valid :=
  Action.check_sound _ (by decide +kernel)

def action73 : Action := ⟨![0,4,1,2,5,3],false,![2,5,9,7,0,3,1,6,4,8,11,15,13,18,16,19,12,10,14,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action73_valid : action73.Valid :=
  Action.check_sound _ (by decide +kernel)

def action74 : Action := ⟨![0,4,1,3,2,5],false,![2,7,5,9,1,0,3,4,8,6,13,11,15,16,19,18,10,14,12,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action74_valid : action74.Valid :=
  Action.check_sound _ (by decide +kernel)

def action75 : Action := ⟨![0,4,1,3,5,2],false,![2,7,9,5,1,3,0,8,4,6,13,15,11,19,16,18,14,10,12,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action75_valid : action75.Valid :=
  Action.check_sound _ (by decide +kernel)

def action76 : Action := ⟨![0,4,1,5,2,3],false,![2,9,5,7,3,0,1,6,8,4,15,11,13,18,19,16,12,14,10,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action76_valid : action76.Valid :=
  Action.check_sound _ (by decide +kernel)

def action77 : Action := ⟨![0,4,1,5,3,2],false,![2,9,7,5,3,1,0,8,6,4,15,13,11,19,18,16,14,12,10,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action77_valid : action77.Valid :=
  Action.check_sound _ (by decide +kernel)

def action78 : Action := ⟨![0,4,2,1,3,5],false,![5,2,7,9,0,4,6,1,3,8,11,16,18,13,15,19,10,12,17,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action78_valid : action78.Valid :=
  Action.check_sound _ (by decide +kernel)

def action79 : Action := ⟨![0,4,2,1,5,3],false,![5,2,9,7,0,6,4,3,1,8,11,18,16,15,13,19,12,10,17,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action79_valid : action79.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
