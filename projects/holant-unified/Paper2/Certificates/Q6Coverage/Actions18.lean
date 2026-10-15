import Paper2.Certificates.Q6Coverage.Actions17

namespace Paper2.Certificates.Q6.Coverage

def action288 : Action := ⟨![2,4,3,5,0,1],false,![16,18,5,11,17,4,10,6,12,0,19,7,13,9,15,2,8,14,1,3]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action288_valid : action288.Valid :=
  Action.check_sound _ (by decide +kernel)

def action289 : Action := ⟨![2,4,3,5,1,0],false,![16,18,11,5,17,10,4,12,6,0,19,13,7,15,9,2,14,8,1,3]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action289_valid : action289.Valid :=
  Action.check_sound _ (by decide +kernel)

def action290 : Action := ⟨![2,4,5,0,1,3],false,![18,5,11,16,6,12,17,0,4,10,9,15,19,2,7,13,3,8,14,1]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action290_valid : action290.Valid :=
  Action.check_sound _ (by decide +kernel)

def action291 : Action := ⟨![2,4,5,0,3,1],false,![18,5,16,11,6,17,12,4,0,10,9,19,15,7,2,13,8,3,14,1]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action291_valid : action291.Valid :=
  Action.check_sound _ (by decide +kernel)

def action292 : Action := ⟨![2,4,5,1,3,0],false,![18,11,16,5,12,17,6,10,0,4,15,19,9,13,2,7,14,3,8,1]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action292_valid : action292.Valid :=
  Action.check_sound _ (by decide +kernel)

def action293 : Action := ⟨![2,4,5,3,0,1],false,![18,16,5,11,17,6,12,4,10,0,19,9,15,7,13,2,8,14,3,1]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action293_valid : action293.Valid :=
  Action.check_sound _ (by decide +kernel)

def action294 : Action := ⟨![2,4,5,3,1,0],false,![18,16,11,5,17,12,6,10,4,0,19,15,9,13,7,2,14,8,3,1]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action294_valid : action294.Valid :=
  Action.check_sound _ (by decide +kernel)

def action295 : Action := ⟨![2,5,0,1,3,4],false,![6,12,17,18,0,4,5,10,11,16,3,8,9,14,15,19,1,2,7,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action295_valid : action295.Valid :=
  Action.check_sound _ (by decide +kernel)

def action296 : Action := ⟨![2,5,0,1,4,3],false,![6,12,18,17,0,5,4,11,10,16,3,9,8,15,14,19,2,1,7,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action296_valid : action296.Valid :=
  Action.check_sound _ (by decide +kernel)

def action297 : Action := ⟨![2,5,0,3,1,4],false,![6,17,12,18,4,0,5,10,16,11,8,3,9,14,19,15,1,7,2,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action297_valid : action297.Valid :=
  Action.check_sound _ (by decide +kernel)

def action298 : Action := ⟨![2,5,0,3,4,1],false,![6,17,18,12,4,5,0,16,10,11,8,9,3,19,14,15,7,1,2,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action298_valid : action298.Valid :=
  Action.check_sound _ (by decide +kernel)

def action299 : Action := ⟨![2,5,0,4,1,3],false,![6,18,12,17,5,0,4,11,16,10,9,3,8,15,19,14,2,7,1,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action299_valid : action299.Valid :=
  Action.check_sound _ (by decide +kernel)

def action300 : Action := ⟨![2,5,0,4,3,1],false,![6,18,17,12,5,4,0,16,11,10,9,8,3,19,15,14,7,2,1,13]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action300_valid : action300.Valid :=
  Action.check_sound _ (by decide +kernel)

def action301 : Action := ⟨![2,5,1,0,3,4],false,![12,6,17,18,0,10,11,4,5,16,3,14,15,8,9,19,1,2,13,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action301_valid : action301.Valid :=
  Action.check_sound _ (by decide +kernel)

def action302 : Action := ⟨![2,5,1,0,4,3],false,![12,6,18,17,0,11,10,5,4,16,3,15,14,9,8,19,2,1,13,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action302_valid : action302.Valid :=
  Action.check_sound _ (by decide +kernel)

def action303 : Action := ⟨![2,5,1,3,0,4],false,![12,17,6,18,10,0,11,4,16,5,14,3,15,8,19,9,1,13,2,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action303_valid : action303.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
