import Paper2.Certificates.Q6Coverage.Actions11

namespace Paper2.Certificates.Q6.Coverage

def action192 : Action := ⟨![1,4,0,2,3,5],false,![2,11,13,15,0,1,3,10,12,14,5,7,9,16,18,19,4,6,8,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action192_valid : action192.Valid :=
  Action.check_sound _ (by decide +kernel)

def action193 : Action := ⟨![1,4,0,2,5,3],false,![2,11,15,13,0,3,1,12,10,14,5,9,7,18,16,19,6,4,8,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action193_valid : action193.Valid :=
  Action.check_sound _ (by decide +kernel)

def action194 : Action := ⟨![1,4,0,3,2,5],false,![2,13,11,15,1,0,3,10,14,12,7,5,9,16,19,18,4,8,6,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action194_valid : action194.Valid :=
  Action.check_sound _ (by decide +kernel)

def action195 : Action := ⟨![1,4,0,3,5,2],false,![2,13,15,11,1,3,0,14,10,12,7,9,5,19,16,18,8,4,6,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action195_valid : action195.Valid :=
  Action.check_sound _ (by decide +kernel)

def action196 : Action := ⟨![1,4,0,5,2,3],false,![2,15,11,13,3,0,1,12,14,10,9,5,7,18,19,16,6,8,4,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action196_valid : action196.Valid :=
  Action.check_sound _ (by decide +kernel)

def action197 : Action := ⟨![1,4,0,5,3,2],false,![2,15,13,11,3,1,0,14,12,10,9,7,5,19,18,16,8,6,4,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action197_valid : action197.Valid :=
  Action.check_sound _ (by decide +kernel)

def action198 : Action := ⟨![1,4,2,0,3,5],false,![11,2,13,15,0,10,12,1,3,14,5,16,18,7,9,19,4,6,17,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action198_valid : action198.Valid :=
  Action.check_sound _ (by decide +kernel)

def action199 : Action := ⟨![1,4,2,0,5,3],false,![11,2,15,13,0,12,10,3,1,14,5,18,16,9,7,19,6,4,17,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action199_valid : action199.Valid :=
  Action.check_sound _ (by decide +kernel)

def action200 : Action := ⟨![1,4,2,3,0,5],false,![11,13,2,15,10,0,12,1,14,3,16,5,18,7,19,9,4,17,6,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action200_valid : action200.Valid :=
  Action.check_sound _ (by decide +kernel)

def action201 : Action := ⟨![1,4,2,3,5,0],false,![11,13,15,2,10,12,0,14,1,3,16,18,5,19,7,9,17,4,6,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action201_valid : action201.Valid :=
  Action.check_sound _ (by decide +kernel)

def action202 : Action := ⟨![1,4,2,5,0,3],false,![11,15,2,13,12,0,10,3,14,1,18,5,16,9,19,7,6,17,4,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action202_valid : action202.Valid :=
  Action.check_sound _ (by decide +kernel)

def action203 : Action := ⟨![1,4,2,5,3,0],false,![11,15,13,2,12,10,0,14,3,1,18,16,5,19,9,7,17,6,4,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action203_valid : action203.Valid :=
  Action.check_sound _ (by decide +kernel)

def action204 : Action := ⟨![1,4,3,0,2,5],false,![13,2,11,15,1,10,14,0,3,12,7,16,19,5,9,18,4,8,17,6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action204_valid : action204.Valid :=
  Action.check_sound _ (by decide +kernel)

def action205 : Action := ⟨![1,4,3,0,5,2],false,![13,2,15,11,1,14,10,3,0,12,7,19,16,9,5,18,8,4,17,6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action205_valid : action205.Valid :=
  Action.check_sound _ (by decide +kernel)

def action206 : Action := ⟨![1,4,3,2,0,5],false,![13,11,2,15,10,1,14,0,12,3,16,7,19,5,18,9,4,17,8,6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action206_valid : action206.Valid :=
  Action.check_sound _ (by decide +kernel)

def action207 : Action := ⟨![1,4,3,2,5,0],false,![13,11,15,2,10,14,1,12,0,3,16,19,7,18,5,9,17,4,8,6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action207_valid : action207.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
