import Paper2.Certificates.Q6Coverage.Actions12

namespace Paper2.Certificates.Q6.Coverage

def action208 : Action := ⟨![1,4,3,5,0,2],false,![13,15,2,11,14,1,10,3,12,0,19,7,16,9,18,5,8,17,4,6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action208_valid : action208.Valid :=
  Action.check_sound _ (by decide +kernel)

def action209 : Action := ⟨![1,4,3,5,2,0],false,![13,15,11,2,14,10,1,12,3,0,19,16,7,18,9,5,17,8,4,6]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action209_valid : action209.Valid :=
  Action.check_sound _ (by decide +kernel)

def action210 : Action := ⟨![1,4,5,0,2,3],false,![15,2,11,13,3,12,14,0,1,10,9,18,19,5,7,16,6,8,17,4]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action210_valid : action210.Valid :=
  Action.check_sound _ (by decide +kernel)

def action211 : Action := ⟨![1,4,5,0,3,2],false,![15,2,13,11,3,14,12,1,0,10,9,19,18,7,5,16,8,6,17,4]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action211_valid : action211.Valid :=
  Action.check_sound _ (by decide +kernel)

def action212 : Action := ⟨![1,4,5,2,0,3],false,![15,11,2,13,12,3,14,0,10,1,18,9,19,5,16,7,6,17,8,4]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action212_valid : action212.Valid :=
  Action.check_sound _ (by decide +kernel)

def action213 : Action := ⟨![1,4,5,2,3,0],false,![15,11,13,2,12,14,3,10,0,1,18,19,9,16,5,7,17,6,8,4]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action213_valid : action213.Valid :=
  Action.check_sound _ (by decide +kernel)

def action214 : Action := ⟨![1,4,5,3,0,2],false,![15,13,2,11,14,3,12,1,10,0,19,9,18,7,16,5,8,17,6,4]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action214_valid : action214.Valid :=
  Action.check_sound _ (by decide +kernel)

def action215 : Action := ⟨![1,4,5,3,2,0],false,![15,13,11,2,14,12,3,10,1,0,19,18,9,16,7,5,17,8,6,4]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action215_valid : action215.Valid :=
  Action.check_sound _ (by decide +kernel)

def action216 : Action := ⟨![1,5,0,2,3,4],false,![3,12,14,15,0,1,2,10,11,13,6,8,9,17,18,19,4,5,7,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action216_valid : action216.Valid :=
  Action.check_sound _ (by decide +kernel)

def action217 : Action := ⟨![1,5,0,2,4,3],false,![3,12,15,14,0,2,1,11,10,13,6,9,8,18,17,19,5,4,7,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action217_valid : action217.Valid :=
  Action.check_sound _ (by decide +kernel)

def action218 : Action := ⟨![1,5,0,3,2,4],false,![3,14,12,15,1,0,2,10,13,11,8,6,9,17,19,18,4,7,5,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action218_valid : action218.Valid :=
  Action.check_sound _ (by decide +kernel)

def action219 : Action := ⟨![1,5,0,3,4,2],false,![3,14,15,12,1,2,0,13,10,11,8,9,6,19,17,18,7,4,5,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action219_valid : action219.Valid :=
  Action.check_sound _ (by decide +kernel)

def action220 : Action := ⟨![1,5,0,4,2,3],false,![3,15,12,14,2,0,1,11,13,10,9,6,8,18,19,17,5,7,4,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action220_valid : action220.Valid :=
  Action.check_sound _ (by decide +kernel)

def action221 : Action := ⟨![1,5,0,4,3,2],false,![3,15,14,12,2,1,0,13,11,10,9,8,6,19,18,17,7,5,4,16]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action221_valid : action221.Valid :=
  Action.check_sound _ (by decide +kernel)

def action222 : Action := ⟨![1,5,2,0,3,4],false,![12,3,14,15,0,10,11,1,2,13,6,17,18,8,9,19,4,5,16,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action222_valid : action222.Valid :=
  Action.check_sound _ (by decide +kernel)

def action223 : Action := ⟨![1,5,2,0,4,3],false,![12,3,15,14,0,11,10,2,1,13,6,18,17,9,8,19,5,4,16,7]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action223_valid : action223.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
