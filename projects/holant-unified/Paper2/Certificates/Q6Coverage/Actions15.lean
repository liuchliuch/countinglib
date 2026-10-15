import Paper2.Certificates.Q6Coverage.Actions14

namespace Paper2.Certificates.Q6.Coverage

def action240 : Action := ⟨![2,0,3,4,1,5],false,![4,5,0,6,16,10,17,11,18,12,7,1,8,2,9,3,13,19,14,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action240_valid : action240.Valid :=
  Action.check_sound _ (by decide +kernel)

def action241 : Action := ⟨![2,0,3,5,1,4],false,![4,6,0,5,17,10,16,12,18,11,8,1,7,3,9,2,14,19,13,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action241_valid : action241.Valid :=
  Action.check_sound _ (by decide +kernel)

def action242 : Action := ⟨![2,0,4,3,1,5],false,![5,4,0,6,16,11,18,10,17,12,7,2,9,1,8,3,13,19,15,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action242_valid : action242.Valid :=
  Action.check_sound _ (by decide +kernel)

def action243 : Action := ⟨![2,0,4,5,1,3],false,![5,6,0,4,18,11,16,12,17,10,9,2,7,3,8,1,15,19,13,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action243_valid : action243.Valid :=
  Action.check_sound _ (by decide +kernel)

def action244 : Action := ⟨![2,0,5,3,1,4],false,![6,4,0,5,17,12,18,10,16,11,8,3,9,1,7,2,14,19,15,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action244_valid : action244.Valid :=
  Action.check_sound _ (by decide +kernel)

def action245 : Action := ⟨![2,0,5,4,1,3],false,![6,5,0,4,18,12,17,11,16,10,9,3,8,2,7,1,15,19,14,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action245_valid : action245.Valid :=
  Action.check_sound _ (by decide +kernel)

def action246 : Action := ⟨![2,1,3,4,0,5],false,![10,11,0,12,16,4,17,5,18,6,13,1,14,2,15,3,7,19,8,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action246_valid : action246.Valid :=
  Action.check_sound _ (by decide +kernel)

def action247 : Action := ⟨![2,1,3,5,0,4],false,![10,12,0,11,17,4,16,6,18,5,14,1,13,3,15,2,8,19,7,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action247_valid : action247.Valid :=
  Action.check_sound _ (by decide +kernel)

def action248 : Action := ⟨![2,1,4,3,0,5],false,![11,10,0,12,16,5,18,4,17,6,13,2,15,1,14,3,7,19,9,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action248_valid : action248.Valid :=
  Action.check_sound _ (by decide +kernel)

def action249 : Action := ⟨![2,1,4,5,0,3],false,![11,12,0,10,18,5,16,6,17,4,15,2,13,3,14,1,9,19,7,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action249_valid : action249.Valid :=
  Action.check_sound _ (by decide +kernel)

def action250 : Action := ⟨![2,1,5,3,0,4],false,![12,10,0,11,17,6,18,4,16,5,14,3,15,1,13,2,8,19,9,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action250_valid : action250.Valid :=
  Action.check_sound _ (by decide +kernel)

def action251 : Action := ⟨![2,1,5,4,0,3],false,![12,11,0,10,18,6,17,5,16,4,15,3,14,2,13,1,9,19,8,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action251_valid : action251.Valid :=
  Action.check_sound _ (by decide +kernel)

def action252 : Action := ⟨![2,3,0,1,4,5],false,![4,10,16,17,0,5,6,11,12,18,1,7,8,13,14,19,2,3,9,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action252_valid : action252.Valid :=
  Action.check_sound _ (by decide +kernel)

def action253 : Action := ⟨![2,3,0,1,5,4],false,![4,10,17,16,0,6,5,12,11,18,1,8,7,14,13,19,3,2,9,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action253_valid : action253.Valid :=
  Action.check_sound _ (by decide +kernel)

def action254 : Action := ⟨![2,3,0,4,1,5],false,![4,16,10,17,5,0,6,11,18,12,7,1,8,13,19,14,2,9,3,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action254_valid : action254.Valid :=
  Action.check_sound _ (by decide +kernel)

def action255 : Action := ⟨![2,3,0,4,5,1],false,![4,16,17,10,5,6,0,18,11,12,7,8,1,19,13,14,9,2,3,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action255_valid : action255.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
