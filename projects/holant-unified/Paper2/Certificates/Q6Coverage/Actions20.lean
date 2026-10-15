import Paper2.Certificates.Q6Coverage.Actions19

namespace Paper2.Certificates.Q6.Coverage

def action320 : Action := ⟨![3,4,1,0,2,5],false,![13,7,16,19,1,10,14,4,8,17,2,11,15,5,9,18,0,3,12,6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action320_valid : action320.Valid :=
  Action.check_sound _ (by decide +kernel)

def action321 : Action := ⟨![3,4,1,0,5,2],false,![13,7,19,16,1,14,10,8,4,17,2,15,11,9,5,18,3,0,12,6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action321_valid : action321.Valid :=
  Action.check_sound _ (by decide +kernel)

def action322 : Action := ⟨![3,4,1,2,0,5],false,![13,16,7,19,10,1,14,4,17,8,11,2,15,5,18,9,0,12,3,6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action322_valid : action322.Valid :=
  Action.check_sound _ (by decide +kernel)

def action323 : Action := ⟨![3,4,1,2,5,0],false,![13,16,19,7,10,14,1,17,4,8,11,15,2,18,5,9,12,0,3,6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action323_valid : action323.Valid :=
  Action.check_sound _ (by decide +kernel)

def action324 : Action := ⟨![3,4,1,5,0,2],false,![13,19,7,16,14,1,10,8,17,4,15,2,11,9,18,5,3,12,0,6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action324_valid : action324.Valid :=
  Action.check_sound _ (by decide +kernel)

def action325 : Action := ⟨![3,4,1,5,2,0],false,![13,19,16,7,14,10,1,17,8,4,15,11,2,18,9,5,12,3,0,6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action325_valid : action325.Valid :=
  Action.check_sound _ (by decide +kernel)

def action326 : Action := ⟨![3,4,2,0,5,1],false,![16,7,19,13,4,17,10,8,1,14,5,18,11,9,2,15,6,0,12,3]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action326_valid : action326.Valid :=
  Action.check_sound _ (by decide +kernel)

def action327 : Action := ⟨![3,4,2,1,5,0],false,![16,13,19,7,10,17,4,14,1,8,11,18,5,15,2,9,12,0,6,3]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action327_valid : action327.Valid :=
  Action.check_sound _ (by decide +kernel)

def action328 : Action := ⟨![3,4,2,5,0,1],false,![16,19,7,13,17,4,10,8,14,1,18,5,11,9,15,2,6,12,0,3]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action328_valid : action328.Valid :=
  Action.check_sound _ (by decide +kernel)

def action329 : Action := ⟨![3,4,2,5,1,0],false,![16,19,13,7,17,10,4,14,8,1,18,11,5,15,9,2,12,6,0,3]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action329_valid : action329.Valid :=
  Action.check_sound _ (by decide +kernel)

def action330 : Action := ⟨![3,5,0,1,2,4],false,![8,14,17,19,1,4,7,10,13,16,3,6,9,12,15,18,0,2,5,11]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action330_valid : action330.Valid :=
  Action.check_sound _ (by decide +kernel)

def action331 : Action := ⟨![3,5,0,1,4,2],false,![8,14,19,17,1,7,4,13,10,16,3,9,6,15,12,18,2,0,5,11]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action331_valid : action331.Valid :=
  Action.check_sound _ (by decide +kernel)

def action332 : Action := ⟨![3,5,0,2,1,4],false,![8,17,14,19,4,1,7,10,16,13,6,3,9,12,18,15,0,5,2,11]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action332_valid : action332.Valid :=
  Action.check_sound _ (by decide +kernel)

def action333 : Action := ⟨![3,5,0,2,4,1],false,![8,17,19,14,4,7,1,16,10,13,6,9,3,18,12,15,5,0,2,11]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action333_valid : action333.Valid :=
  Action.check_sound _ (by decide +kernel)

def action334 : Action := ⟨![3,5,0,4,1,2],false,![8,19,14,17,7,1,4,13,16,10,9,3,6,15,18,12,2,5,0,11]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action334_valid : action334.Valid :=
  Action.check_sound _ (by decide +kernel)

def action335 : Action := ⟨![3,5,0,4,2,1],false,![8,19,17,14,7,4,1,16,13,10,9,6,3,18,15,12,5,2,0,11]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action335_valid : action335.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
