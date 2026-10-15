import Paper2.Certificates.Q6Coverage.Actions10

namespace Paper2.Certificates.Q6.Coverage

def action176 : Action := ⟨![1,3,2,4,0,5],false,![10,13,1,14,11,0,12,2,15,3,16,4,17,7,19,8,5,18,6,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action176_valid : action176.Valid :=
  Action.check_sound _ (by decide +kernel)

def action177 : Action := ⟨![1,3,2,4,5,0],false,![10,13,14,1,11,12,0,15,2,3,16,17,4,19,7,8,18,5,6,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action177_valid : action177.Valid :=
  Action.check_sound _ (by decide +kernel)

def action178 : Action := ⟨![1,3,2,5,0,4],false,![10,14,1,13,12,0,11,3,15,2,17,4,16,8,19,7,6,18,5,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action178_valid : action178.Valid :=
  Action.check_sound _ (by decide +kernel)

def action179 : Action := ⟨![1,3,2,5,4,0],false,![10,14,13,1,12,11,0,15,3,2,17,16,4,19,8,7,18,6,5,9]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action179_valid : action179.Valid :=
  Action.check_sound _ (by decide +kernel)

def action180 : Action := ⟨![1,3,4,0,2,5],false,![13,1,10,14,2,11,15,0,3,12,7,16,19,4,8,17,5,9,18,6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action180_valid : action180.Valid :=
  Action.check_sound _ (by decide +kernel)

def action181 : Action := ⟨![1,3,4,0,5,2],false,![13,1,14,10,2,15,11,3,0,12,7,19,16,8,4,17,9,5,18,6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action181_valid : action181.Valid :=
  Action.check_sound _ (by decide +kernel)

def action182 : Action := ⟨![1,3,4,2,0,5],false,![13,10,1,14,11,2,15,0,12,3,16,7,19,4,17,8,5,18,9,6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action182_valid : action182.Valid :=
  Action.check_sound _ (by decide +kernel)

def action183 : Action := ⟨![1,3,4,2,5,0],false,![13,10,14,1,11,15,2,12,0,3,16,19,7,17,4,8,18,5,9,6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action183_valid : action183.Valid :=
  Action.check_sound _ (by decide +kernel)

def action184 : Action := ⟨![1,3,4,5,0,2],false,![13,14,1,10,15,2,11,3,12,0,19,7,16,8,17,4,9,18,5,6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action184_valid : action184.Valid :=
  Action.check_sound _ (by decide +kernel)

def action185 : Action := ⟨![1,3,4,5,2,0],false,![13,14,10,1,15,11,2,12,3,0,19,16,7,17,8,4,18,9,5,6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action185_valid : action185.Valid :=
  Action.check_sound _ (by decide +kernel)

def action186 : Action := ⟨![1,3,5,0,2,4],false,![14,1,10,13,3,12,15,0,2,11,8,17,19,4,7,16,6,9,18,5]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action186_valid : action186.Valid :=
  Action.check_sound _ (by decide +kernel)

def action187 : Action := ⟨![1,3,5,0,4,2],false,![14,1,13,10,3,15,12,2,0,11,8,19,17,7,4,16,9,6,18,5]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action187_valid : action187.Valid :=
  Action.check_sound _ (by decide +kernel)

def action188 : Action := ⟨![1,3,5,2,0,4],false,![14,10,1,13,12,3,15,0,11,2,17,8,19,4,16,7,6,18,9,5]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action188_valid : action188.Valid :=
  Action.check_sound _ (by decide +kernel)

def action189 : Action := ⟨![1,3,5,2,4,0],false,![14,10,13,1,12,15,3,11,0,2,17,19,8,16,4,7,18,6,9,5]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action189_valid : action189.Valid :=
  Action.check_sound _ (by decide +kernel)

def action190 : Action := ⟨![1,3,5,4,0,2],false,![14,13,1,10,15,3,12,2,11,0,19,8,17,7,16,4,9,18,6,5]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action190_valid : action190.Valid :=
  Action.check_sound _ (by decide +kernel)

def action191 : Action := ⟨![1,3,5,4,2,0],false,![14,13,10,1,15,12,3,11,2,0,19,17,8,16,7,4,18,9,6,5]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action191_valid : action191.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
