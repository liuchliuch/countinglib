import Paper2.Certificates.Q6Coverage.Actions20

namespace Paper2.Certificates.Q6.Coverage

def action336 : Action := ⟨![3,5,1,0,2,4],false,![14,8,17,19,1,10,13,4,7,16,3,12,15,6,9,18,0,2,11,5]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action336_valid : action336.Valid :=
  Action.check_sound _ (by decide +kernel)

def action337 : Action := ⟨![3,5,1,0,4,2],false,![14,8,19,17,1,13,10,7,4,16,3,15,12,9,6,18,2,0,11,5]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action337_valid : action337.Valid :=
  Action.check_sound _ (by decide +kernel)

def action338 : Action := ⟨![3,5,1,2,0,4],false,![14,17,8,19,10,1,13,4,16,7,12,3,15,6,18,9,0,11,2,5]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action338_valid : action338.Valid :=
  Action.check_sound _ (by decide +kernel)

def action339 : Action := ⟨![3,5,1,2,4,0],false,![14,17,19,8,10,13,1,16,4,7,12,15,3,18,6,9,11,0,2,5]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action339_valid : action339.Valid :=
  Action.check_sound _ (by decide +kernel)

def action340 : Action := ⟨![3,5,1,4,0,2],false,![14,19,8,17,13,1,10,7,16,4,15,3,12,9,18,6,2,11,0,5]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action340_valid : action340.Valid :=
  Action.check_sound _ (by decide +kernel)

def action341 : Action := ⟨![3,5,1,4,2,0],false,![14,19,17,8,13,10,1,16,7,4,15,12,3,18,9,6,11,2,0,5]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action341_valid : action341.Valid :=
  Action.check_sound _ (by decide +kernel)

def action342 : Action := ⟨![3,5,2,0,4,1],false,![17,8,19,14,4,16,10,7,1,13,6,18,12,9,3,15,5,0,11,2]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action342_valid : action342.Valid :=
  Action.check_sound _ (by decide +kernel)

def action343 : Action := ⟨![3,5,2,1,4,0],false,![17,14,19,8,10,16,4,13,1,7,12,18,6,15,3,9,11,0,5,2]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action343_valid : action343.Valid :=
  Action.check_sound _ (by decide +kernel)

def action344 : Action := ⟨![3,5,2,4,0,1],false,![17,19,8,14,16,4,10,7,13,1,18,6,12,9,15,3,5,11,0,2]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action344_valid : action344.Valid :=
  Action.check_sound _ (by decide +kernel)

def action345 : Action := ⟨![3,5,2,4,1,0],false,![17,19,14,8,16,10,4,13,7,1,18,12,6,15,9,3,11,5,0,2]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action345_valid : action345.Valid :=
  Action.check_sound _ (by decide +kernel)

def action346 : Action := ⟨![4,5,0,1,2,3],false,![9,15,18,19,2,5,7,11,13,16,3,6,8,12,14,17,0,1,4,10]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action346_valid : action346.Valid :=
  Action.check_sound _ (by decide +kernel)

def action347 : Action := ⟨![4,5,0,1,3,2],false,![9,15,19,18,2,7,5,13,11,16,3,8,6,14,12,17,1,0,4,10]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action347_valid : action347.Valid :=
  Action.check_sound _ (by decide +kernel)

def action348 : Action := ⟨![4,5,0,2,1,3],false,![9,18,15,19,5,2,7,11,16,13,6,3,8,12,17,14,0,4,1,10]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action348_valid : action348.Valid :=
  Action.check_sound _ (by decide +kernel)

def action349 : Action := ⟨![4,5,0,2,3,1],false,![9,18,19,15,5,7,2,16,11,13,6,8,3,17,12,14,4,0,1,10]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action349_valid : action349.Valid :=
  Action.check_sound _ (by decide +kernel)

def action350 : Action := ⟨![4,5,0,3,1,2],false,![9,19,15,18,7,2,5,13,16,11,8,3,6,14,17,12,1,4,0,10]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action350_valid : action350.Valid :=
  Action.check_sound _ (by decide +kernel)

def action351 : Action := ⟨![4,5,0,3,2,1],false,![9,19,18,15,7,5,2,16,13,11,8,6,3,17,14,12,4,1,0,10]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action351_valid : action351.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
