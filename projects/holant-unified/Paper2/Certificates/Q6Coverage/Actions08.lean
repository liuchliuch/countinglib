import Paper2.Certificates.Q6Coverage.Actions07

namespace Paper2.Certificates.Q6.Coverage

def action128 : Action := ⟨![1,0,3,4,2,5],false,![1,2,0,3,13,10,14,11,15,12,7,4,8,5,9,6,16,19,17,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action128_valid : action128.Valid :=
  Action.check_sound _ (by decide +kernel)

def action129 : Action := ⟨![1,0,3,4,5,2],false,![1,2,3,0,13,14,10,15,11,12,7,8,4,9,5,6,19,16,17,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action129_valid : action129.Valid :=
  Action.check_sound _ (by decide +kernel)

def action130 : Action := ⟨![1,0,3,5,2,4],false,![1,3,0,2,14,10,13,12,15,11,8,4,7,6,9,5,17,19,16,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action130_valid : action130.Valid :=
  Action.check_sound _ (by decide +kernel)

def action131 : Action := ⟨![1,0,3,5,4,2],false,![1,3,2,0,14,13,10,15,12,11,8,7,4,9,6,5,19,17,16,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action131_valid : action131.Valid :=
  Action.check_sound _ (by decide +kernel)

def action132 : Action := ⟨![1,0,4,2,3,5],false,![2,0,1,3,11,13,15,10,12,14,5,7,9,4,6,8,16,18,19,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action132_valid : action132.Valid :=
  Action.check_sound _ (by decide +kernel)

def action133 : Action := ⟨![1,0,4,2,5,3],false,![2,0,3,1,11,15,13,12,10,14,5,9,7,6,4,8,18,16,19,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action133_valid : action133.Valid :=
  Action.check_sound _ (by decide +kernel)

def action134 : Action := ⟨![1,0,4,3,2,5],false,![2,1,0,3,13,11,15,10,14,12,7,5,9,4,8,6,16,19,18,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action134_valid : action134.Valid :=
  Action.check_sound _ (by decide +kernel)

def action135 : Action := ⟨![1,0,4,3,5,2],false,![2,1,3,0,13,15,11,14,10,12,7,9,5,8,4,6,19,16,18,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action135_valid : action135.Valid :=
  Action.check_sound _ (by decide +kernel)

def action136 : Action := ⟨![1,0,4,5,2,3],false,![2,3,0,1,15,11,13,12,14,10,9,5,7,6,8,4,18,19,16,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action136_valid : action136.Valid :=
  Action.check_sound _ (by decide +kernel)

def action137 : Action := ⟨![1,0,4,5,3,2],false,![2,3,1,0,15,13,11,14,12,10,9,7,5,8,6,4,19,18,16,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action137_valid : action137.Valid :=
  Action.check_sound _ (by decide +kernel)

def action138 : Action := ⟨![1,0,5,2,3,4],false,![3,0,1,2,12,14,15,10,11,13,6,8,9,4,5,7,17,18,19,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action138_valid : action138.Valid :=
  Action.check_sound _ (by decide +kernel)

def action139 : Action := ⟨![1,0,5,2,4,3],false,![3,0,2,1,12,15,14,11,10,13,6,9,8,5,4,7,18,17,19,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action139_valid : action139.Valid :=
  Action.check_sound _ (by decide +kernel)

def action140 : Action := ⟨![1,0,5,3,2,4],false,![3,1,0,2,14,12,15,10,13,11,8,6,9,4,7,5,17,19,18,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action140_valid : action140.Valid :=
  Action.check_sound _ (by decide +kernel)

def action141 : Action := ⟨![1,0,5,3,4,2],false,![3,1,2,0,14,15,12,13,10,11,8,9,6,7,4,5,19,17,18,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action141_valid : action141.Valid :=
  Action.check_sound _ (by decide +kernel)

def action142 : Action := ⟨![1,0,5,4,2,3],false,![3,2,0,1,15,12,14,11,13,10,9,6,8,5,7,4,18,19,17,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action142_valid : action142.Valid :=
  Action.check_sound _ (by decide +kernel)

def action143 : Action := ⟨![1,0,5,4,3,2],false,![3,2,1,0,15,14,12,13,11,10,9,8,6,7,5,4,19,18,17,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action143_valid : action143.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
