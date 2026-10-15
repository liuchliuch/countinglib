import Paper2.Certificates.Q6Coverage.Rows

namespace Paper2.Certificates.Q6.Coverage

def action0 : Action := ⟨![0,1,2,3,4,5],false,![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action0_valid : action0.Valid :=
  Action.check_sound _ (by decide +kernel)

def action1 : Action := ⟨![0,1,2,3,5,4],false,![0,1,3,2,4,6,5,8,7,9,10,12,11,14,13,15,17,16,18,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action1_valid : action1.Valid :=
  Action.check_sound _ (by decide +kernel)

def action2 : Action := ⟨![0,1,2,4,3,5],false,![0,2,1,3,5,4,6,7,9,8,11,10,12,13,15,14,16,18,17,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action2_valid : action2.Valid :=
  Action.check_sound _ (by decide +kernel)

def action3 : Action := ⟨![0,1,2,4,5,3],false,![0,2,3,1,5,6,4,9,7,8,11,12,10,15,13,14,18,16,17,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action3_valid : action3.Valid :=
  Action.check_sound _ (by decide +kernel)

def action4 : Action := ⟨![0,1,2,5,3,4],false,![0,3,1,2,6,4,5,8,9,7,12,10,11,14,15,13,17,18,16,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action4_valid : action4.Valid :=
  Action.check_sound _ (by decide +kernel)

def action5 : Action := ⟨![0,1,2,5,4,3],false,![0,3,2,1,6,5,4,9,8,7,12,11,10,15,14,13,18,17,16,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action5_valid : action5.Valid :=
  Action.check_sound _ (by decide +kernel)

def action6 : Action := ⟨![0,1,3,2,4,5],false,![1,0,2,3,4,7,8,5,6,9,10,13,14,11,12,15,16,17,19,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action6_valid : action6.Valid :=
  Action.check_sound _ (by decide +kernel)

def action7 : Action := ⟨![0,1,3,2,5,4],false,![1,0,3,2,4,8,7,6,5,9,10,14,13,12,11,15,17,16,19,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action7_valid : action7.Valid :=
  Action.check_sound _ (by decide +kernel)

def action8 : Action := ⟨![0,1,3,4,2,5],false,![1,2,0,3,7,4,8,5,9,6,13,10,14,11,15,12,16,19,17,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action8_valid : action8.Valid :=
  Action.check_sound _ (by decide +kernel)

def action9 : Action := ⟨![0,1,3,4,5,2],false,![1,2,3,0,7,8,4,9,5,6,13,14,10,15,11,12,19,16,17,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action9_valid : action9.Valid :=
  Action.check_sound _ (by decide +kernel)

def action10 : Action := ⟨![0,1,3,5,2,4],false,![1,3,0,2,8,4,7,6,9,5,14,10,13,12,15,11,17,19,16,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action10_valid : action10.Valid :=
  Action.check_sound _ (by decide +kernel)

def action11 : Action := ⟨![0,1,3,5,4,2],false,![1,3,2,0,8,7,4,9,6,5,14,13,10,15,12,11,19,17,16,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action11_valid : action11.Valid :=
  Action.check_sound _ (by decide +kernel)

def action12 : Action := ⟨![0,1,4,2,3,5],false,![2,0,1,3,5,7,9,4,6,8,11,13,15,10,12,14,16,18,19,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action12_valid : action12.Valid :=
  Action.check_sound _ (by decide +kernel)

def action13 : Action := ⟨![0,1,4,2,5,3],false,![2,0,3,1,5,9,7,6,4,8,11,15,13,12,10,14,18,16,19,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action13_valid : action13.Valid :=
  Action.check_sound _ (by decide +kernel)

def action14 : Action := ⟨![0,1,4,3,2,5],false,![2,1,0,3,7,5,9,4,8,6,13,11,15,10,14,12,16,19,18,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action14_valid : action14.Valid :=
  Action.check_sound _ (by decide +kernel)

def action15 : Action := ⟨![0,1,4,3,5,2],false,![2,1,3,0,7,9,5,8,4,6,13,15,11,14,10,12,19,16,18,17]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action15_valid : action15.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
