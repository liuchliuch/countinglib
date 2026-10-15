import Paper2.Certificates.Q6Coverage.Actions13

namespace Paper2.Certificates.Q6.Coverage

def action224 : Action := ⟨![1,5,2,3,0,4],false,![12,14,3,15,10,0,11,1,13,2,17,6,18,8,19,9,4,16,5,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action224_valid : action224.Valid :=
  Action.check_sound _ (by decide +kernel)

def action225 : Action := ⟨![1,5,2,3,4,0],false,![12,14,15,3,10,11,0,13,1,2,17,18,6,19,8,9,16,4,5,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action225_valid : action225.Valid :=
  Action.check_sound _ (by decide +kernel)

def action226 : Action := ⟨![1,5,2,4,0,3],false,![12,15,3,14,11,0,10,2,13,1,18,6,17,9,19,8,5,16,4,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action226_valid : action226.Valid :=
  Action.check_sound _ (by decide +kernel)

def action227 : Action := ⟨![1,5,2,4,3,0],false,![12,15,14,3,11,10,0,13,2,1,18,17,6,19,9,8,16,5,4,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action227_valid : action227.Valid :=
  Action.check_sound _ (by decide +kernel)

def action228 : Action := ⟨![1,5,3,0,2,4],false,![14,3,12,15,1,10,13,0,2,11,8,17,19,6,9,18,4,7,16,5]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action228_valid : action228.Valid :=
  Action.check_sound _ (by decide +kernel)

def action229 : Action := ⟨![1,5,3,0,4,2],false,![14,3,15,12,1,13,10,2,0,11,8,19,17,9,6,18,7,4,16,5]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action229_valid : action229.Valid :=
  Action.check_sound _ (by decide +kernel)

def action230 : Action := ⟨![1,5,3,2,0,4],false,![14,12,3,15,10,1,13,0,11,2,17,8,19,6,18,9,4,16,7,5]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action230_valid : action230.Valid :=
  Action.check_sound _ (by decide +kernel)

def action231 : Action := ⟨![1,5,3,2,4,0],false,![14,12,15,3,10,13,1,11,0,2,17,19,8,18,6,9,16,4,7,5]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action231_valid : action231.Valid :=
  Action.check_sound _ (by decide +kernel)

def action232 : Action := ⟨![1,5,3,4,0,2],false,![14,15,3,12,13,1,10,2,11,0,19,8,17,9,18,6,7,16,4,5]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action232_valid : action232.Valid :=
  Action.check_sound _ (by decide +kernel)

def action233 : Action := ⟨![1,5,3,4,2,0],false,![14,15,12,3,13,10,1,11,2,0,19,17,8,18,9,6,16,7,4,5]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action233_valid : action233.Valid :=
  Action.check_sound _ (by decide +kernel)

def action234 : Action := ⟨![1,5,4,0,2,3],false,![15,3,12,14,2,11,13,0,1,10,9,18,19,6,8,17,5,7,16,4]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action234_valid : action234.Valid :=
  Action.check_sound _ (by decide +kernel)

def action235 : Action := ⟨![1,5,4,0,3,2],false,![15,3,14,12,2,13,11,1,0,10,9,19,18,8,6,17,7,5,16,4]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action235_valid : action235.Valid :=
  Action.check_sound _ (by decide +kernel)

def action236 : Action := ⟨![1,5,4,2,0,3],false,![15,12,3,14,11,2,13,0,10,1,18,9,19,6,17,8,5,16,7,4]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action236_valid : action236.Valid :=
  Action.check_sound _ (by decide +kernel)

def action237 : Action := ⟨![1,5,4,2,3,0],false,![15,12,14,3,11,13,2,10,0,1,18,19,9,17,6,8,16,5,7,4]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action237_valid : action237.Valid :=
  Action.check_sound _ (by decide +kernel)

def action238 : Action := ⟨![1,5,4,3,0,2],false,![15,14,3,12,13,2,11,1,10,0,19,9,18,8,17,6,7,16,5,4]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action238_valid : action238.Valid :=
  Action.check_sound _ (by decide +kernel)

def action239 : Action := ⟨![1,5,4,3,2,0],false,![15,14,12,3,13,11,2,10,1,0,19,18,9,17,8,6,16,7,5,4]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action239_valid : action239.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
