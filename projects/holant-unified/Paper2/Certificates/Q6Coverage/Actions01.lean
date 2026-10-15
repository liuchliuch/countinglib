import Paper2.Certificates.Q6Coverage.Actions00

namespace Paper2.Certificates.Q6.Coverage

def action16 : Action := ⟨![0,1,4,5,2,3],false,![2,3,0,1,9,5,7,6,8,4,15,11,13,12,14,10,18,19,16,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action16_valid : action16.Valid :=
  Action.check_sound _ (by decide +kernel)

def action17 : Action := ⟨![0,1,4,5,3,2],false,![2,3,1,0,9,7,5,8,6,4,15,13,11,14,12,10,19,18,16,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action17_valid : action17.Valid :=
  Action.check_sound _ (by decide +kernel)

def action18 : Action := ⟨![0,1,5,2,3,4],false,![3,0,1,2,6,8,9,4,5,7,12,14,15,10,11,13,17,18,19,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action18_valid : action18.Valid :=
  Action.check_sound _ (by decide +kernel)

def action19 : Action := ⟨![0,1,5,2,4,3],false,![3,0,2,1,6,9,8,5,4,7,12,15,14,11,10,13,18,17,19,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action19_valid : action19.Valid :=
  Action.check_sound _ (by decide +kernel)

def action20 : Action := ⟨![0,1,5,3,2,4],false,![3,1,0,2,8,6,9,4,7,5,14,12,15,10,13,11,17,19,18,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action20_valid : action20.Valid :=
  Action.check_sound _ (by decide +kernel)

def action21 : Action := ⟨![0,1,5,3,4,2],false,![3,1,2,0,8,9,6,7,4,5,14,15,12,13,10,11,19,17,18,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action21_valid : action21.Valid :=
  Action.check_sound _ (by decide +kernel)

def action22 : Action := ⟨![0,1,5,4,2,3],false,![3,2,0,1,9,6,8,5,7,4,15,12,14,11,13,10,18,19,17,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action22_valid : action22.Valid :=
  Action.check_sound _ (by decide +kernel)

def action23 : Action := ⟨![0,1,5,4,3,2],false,![3,2,1,0,9,8,6,7,5,4,15,14,12,13,11,10,19,18,17,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action23_valid : action23.Valid :=
  Action.check_sound _ (by decide +kernel)

def action24 : Action := ⟨![0,2,1,3,4,5],false,![0,4,5,6,1,2,3,7,8,9,10,11,12,16,17,18,13,14,15,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action24_valid : action24.Valid :=
  Action.check_sound _ (by decide +kernel)

def action25 : Action := ⟨![0,2,1,3,5,4],false,![0,4,6,5,1,3,2,8,7,9,10,12,11,17,16,18,14,13,15,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action25_valid : action25.Valid :=
  Action.check_sound _ (by decide +kernel)

def action26 : Action := ⟨![0,2,1,4,3,5],false,![0,5,4,6,2,1,3,7,9,8,11,10,12,16,18,17,13,15,14,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action26_valid : action26.Valid :=
  Action.check_sound _ (by decide +kernel)

def action27 : Action := ⟨![0,2,1,4,5,3],false,![0,5,6,4,2,3,1,9,7,8,11,12,10,18,16,17,15,13,14,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action27_valid : action27.Valid :=
  Action.check_sound _ (by decide +kernel)

def action28 : Action := ⟨![0,2,1,5,3,4],false,![0,6,4,5,3,1,2,8,9,7,12,10,11,17,18,16,14,15,13,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action28_valid : action28.Valid :=
  Action.check_sound _ (by decide +kernel)

def action29 : Action := ⟨![0,2,1,5,4,3],false,![0,6,5,4,3,2,1,9,8,7,12,11,10,18,17,16,15,14,13,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action29_valid : action29.Valid :=
  Action.check_sound _ (by decide +kernel)

def action30 : Action := ⟨![0,2,3,1,4,5],false,![4,0,5,6,1,7,8,2,3,9,10,16,17,11,12,18,13,14,19,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action30_valid : action30.Valid :=
  Action.check_sound _ (by decide +kernel)

def action31 : Action := ⟨![0,2,3,1,5,4],false,![4,0,6,5,1,8,7,3,2,9,10,17,16,12,11,18,14,13,19,15]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action31_valid : action31.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
