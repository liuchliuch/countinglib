import Paper2.Certificates.Q6Coverage.Actions08

namespace Paper2.Certificates.Q6.Coverage

def action144 : Action := ⟨![1,2,0,3,4,5],false,![0,10,11,12,1,2,3,13,14,15,4,5,6,16,17,18,7,8,9,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action144_valid : action144.Valid :=
  Action.check_sound _ (by decide +kernel)

def action145 : Action := ⟨![1,2,0,3,5,4],false,![0,10,12,11,1,3,2,14,13,15,4,6,5,17,16,18,8,7,9,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action145_valid : action145.Valid :=
  Action.check_sound _ (by decide +kernel)

def action146 : Action := ⟨![1,2,0,4,3,5],false,![0,11,10,12,2,1,3,13,15,14,5,4,6,16,18,17,7,9,8,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action146_valid : action146.Valid :=
  Action.check_sound _ (by decide +kernel)

def action147 : Action := ⟨![1,2,0,4,5,3],false,![0,11,12,10,2,3,1,15,13,14,5,6,4,18,16,17,9,7,8,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action147_valid : action147.Valid :=
  Action.check_sound _ (by decide +kernel)

def action148 : Action := ⟨![1,2,0,5,3,4],false,![0,12,10,11,3,1,2,14,15,13,6,4,5,17,18,16,8,9,7,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action148_valid : action148.Valid :=
  Action.check_sound _ (by decide +kernel)

def action149 : Action := ⟨![1,2,0,5,4,3],false,![0,12,11,10,3,2,1,15,14,13,6,5,4,18,17,16,9,8,7,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action149_valid : action149.Valid :=
  Action.check_sound _ (by decide +kernel)

def action150 : Action := ⟨![1,2,3,0,4,5],false,![10,0,11,12,1,13,14,2,3,15,4,16,17,5,6,18,7,8,19,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action150_valid : action150.Valid :=
  Action.check_sound _ (by decide +kernel)

def action151 : Action := ⟨![1,2,3,0,5,4],false,![10,0,12,11,1,14,13,3,2,15,4,17,16,6,5,18,8,7,19,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action151_valid : action151.Valid :=
  Action.check_sound _ (by decide +kernel)

def action152 : Action := ⟨![1,2,3,4,0,5],false,![10,11,0,12,13,1,14,2,15,3,16,4,17,5,18,6,7,19,8,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action152_valid : action152.Valid :=
  Action.check_sound _ (by decide +kernel)

def action153 : Action := ⟨![1,2,3,4,5,0],false,![10,11,12,0,13,14,1,15,2,3,16,17,4,18,5,6,19,7,8,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action153_valid : action153.Valid :=
  Action.check_sound _ (by decide +kernel)

def action154 : Action := ⟨![1,2,3,5,0,4],false,![10,12,0,11,14,1,13,3,15,2,17,4,16,6,18,5,8,19,7,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action154_valid : action154.Valid :=
  Action.check_sound _ (by decide +kernel)

def action155 : Action := ⟨![1,2,3,5,4,0],false,![10,12,11,0,14,13,1,15,3,2,17,16,4,18,6,5,19,8,7,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action155_valid : action155.Valid :=
  Action.check_sound _ (by decide +kernel)

def action156 : Action := ⟨![1,2,4,0,3,5],false,![11,0,10,12,2,13,15,1,3,14,5,16,18,4,6,17,7,9,19,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action156_valid : action156.Valid :=
  Action.check_sound _ (by decide +kernel)

def action157 : Action := ⟨![1,2,4,0,5,3],false,![11,0,12,10,2,15,13,3,1,14,5,18,16,6,4,17,9,7,19,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action157_valid : action157.Valid :=
  Action.check_sound _ (by decide +kernel)

def action158 : Action := ⟨![1,2,4,3,0,5],false,![11,10,0,12,13,2,15,1,14,3,16,5,18,4,17,6,7,19,9,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action158_valid : action158.Valid :=
  Action.check_sound _ (by decide +kernel)

def action159 : Action := ⟨![1,2,4,3,5,0],false,![11,10,12,0,13,15,2,14,1,3,16,18,5,17,4,6,19,7,9,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action159_valid : action159.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
