import Paper2.Certificates.Q6Coverage.Actions09

namespace Paper2.Certificates.Q6.Coverage

def action160 : Action := ⟨![1,2,4,5,0,3],false,![11,12,0,10,15,2,13,3,14,1,18,5,16,6,17,4,9,19,7,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action160_valid : action160.Valid :=
  Action.check_sound _ (by decide +kernel)

def action161 : Action := ⟨![1,2,4,5,3,0],false,![11,12,10,0,15,13,2,14,3,1,18,16,5,17,6,4,19,9,7,8]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action161_valid : action161.Valid :=
  Action.check_sound _ (by decide +kernel)

def action162 : Action := ⟨![1,2,5,0,3,4],false,![12,0,10,11,3,14,15,1,2,13,6,17,18,4,5,16,8,9,19,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action162_valid : action162.Valid :=
  Action.check_sound _ (by decide +kernel)

def action163 : Action := ⟨![1,2,5,0,4,3],false,![12,0,11,10,3,15,14,2,1,13,6,18,17,5,4,16,9,8,19,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action163_valid : action163.Valid :=
  Action.check_sound _ (by decide +kernel)

def action164 : Action := ⟨![1,2,5,3,0,4],false,![12,10,0,11,14,3,15,1,13,2,17,6,18,4,16,5,8,19,9,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action164_valid : action164.Valid :=
  Action.check_sound _ (by decide +kernel)

def action165 : Action := ⟨![1,2,5,3,4,0],false,![12,10,11,0,14,15,3,13,1,2,17,18,6,16,4,5,19,8,9,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action165_valid : action165.Valid :=
  Action.check_sound _ (by decide +kernel)

def action166 : Action := ⟨![1,2,5,4,0,3],false,![12,11,0,10,15,3,14,2,13,1,18,6,17,5,16,4,9,19,8,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action166_valid : action166.Valid :=
  Action.check_sound _ (by decide +kernel)

def action167 : Action := ⟨![1,2,5,4,3,0],false,![12,11,10,0,15,14,3,13,2,1,18,17,6,16,5,4,19,9,8,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action167_valid : action167.Valid :=
  Action.check_sound _ (by decide +kernel)

def action168 : Action := ⟨![1,3,0,2,4,5],false,![1,10,13,14,0,2,3,11,12,15,4,7,8,16,17,19,5,6,9,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action168_valid : action168.Valid :=
  Action.check_sound _ (by decide +kernel)

def action169 : Action := ⟨![1,3,0,2,5,4],false,![1,10,14,13,0,3,2,12,11,15,4,8,7,17,16,19,6,5,9,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action169_valid : action169.Valid :=
  Action.check_sound _ (by decide +kernel)

def action170 : Action := ⟨![1,3,0,4,2,5],false,![1,13,10,14,2,0,3,11,15,12,7,4,8,16,19,17,5,9,6,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action170_valid : action170.Valid :=
  Action.check_sound _ (by decide +kernel)

def action171 : Action := ⟨![1,3,0,4,5,2],false,![1,13,14,10,2,3,0,15,11,12,7,8,4,19,16,17,9,5,6,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action171_valid : action171.Valid :=
  Action.check_sound _ (by decide +kernel)

def action172 : Action := ⟨![1,3,0,5,2,4],false,![1,14,10,13,3,0,2,12,15,11,8,4,7,17,19,16,6,9,5,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action172_valid : action172.Valid :=
  Action.check_sound _ (by decide +kernel)

def action173 : Action := ⟨![1,3,0,5,4,2],false,![1,14,13,10,3,2,0,15,12,11,8,7,4,19,17,16,9,6,5,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action173_valid : action173.Valid :=
  Action.check_sound _ (by decide +kernel)

def action174 : Action := ⟨![1,3,2,0,4,5],false,![10,1,13,14,0,11,12,2,3,15,4,16,17,7,8,19,5,6,18,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action174_valid : action174.Valid :=
  Action.check_sound _ (by decide +kernel)

def action175 : Action := ⟨![1,3,2,0,5,4],false,![10,1,14,13,0,12,11,3,2,15,4,17,16,8,7,19,6,5,18,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action175_valid : action175.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
