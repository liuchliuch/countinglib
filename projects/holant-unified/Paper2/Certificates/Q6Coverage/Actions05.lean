import Paper2.Certificates.Q6Coverage.Actions04

namespace Paper2.Certificates.Q6.Coverage

def action80 : Action := ⟨![0,4,2,3,1,5],false,![5,7,2,9,4,0,6,1,8,3,16,11,18,13,19,15,10,17,12,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action80_valid : action80.Valid :=
  Action.check_sound _ (by decide +kernel)

def action81 : Action := ⟨![0,4,2,3,5,1],false,![5,7,9,2,4,6,0,8,1,3,16,18,11,19,13,15,17,10,12,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action81_valid : action81.Valid :=
  Action.check_sound _ (by decide +kernel)

def action82 : Action := ⟨![0,4,2,5,1,3],false,![5,9,2,7,6,0,4,3,8,1,18,11,16,15,19,13,12,17,10,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action82_valid : action82.Valid :=
  Action.check_sound _ (by decide +kernel)

def action83 : Action := ⟨![0,4,2,5,3,1],false,![5,9,7,2,6,4,0,8,3,1,18,16,11,19,15,13,17,12,10,14]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action83_valid : action83.Valid :=
  Action.check_sound _ (by decide +kernel)

def action84 : Action := ⟨![0,4,3,1,2,5],false,![7,2,5,9,1,4,8,0,3,6,13,16,19,11,15,18,10,14,17,12]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action84_valid : action84.Valid :=
  Action.check_sound _ (by decide +kernel)

def action85 : Action := ⟨![0,4,3,1,5,2],false,![7,2,9,5,1,8,4,3,0,6,13,19,16,15,11,18,14,10,17,12]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action85_valid : action85.Valid :=
  Action.check_sound _ (by decide +kernel)

def action86 : Action := ⟨![0,4,3,2,1,5],false,![7,5,2,9,4,1,8,0,6,3,16,13,19,11,18,15,10,17,14,12]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action86_valid : action86.Valid :=
  Action.check_sound _ (by decide +kernel)

def action87 : Action := ⟨![0,4,3,2,5,1],false,![7,5,9,2,4,8,1,6,0,3,16,19,13,18,11,15,17,10,14,12]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action87_valid : action87.Valid :=
  Action.check_sound _ (by decide +kernel)

def action88 : Action := ⟨![0,4,3,5,1,2],false,![7,9,2,5,8,1,4,3,6,0,19,13,16,15,18,11,14,17,10,12]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action88_valid : action88.Valid :=
  Action.check_sound _ (by decide +kernel)

def action89 : Action := ⟨![0,4,3,5,2,1],false,![7,9,5,2,8,4,1,6,3,0,19,16,13,18,15,11,17,14,10,12]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action89_valid : action89.Valid :=
  Action.check_sound _ (by decide +kernel)

def action90 : Action := ⟨![0,4,5,1,2,3],false,![9,2,5,7,3,6,8,0,1,4,15,18,19,11,13,16,12,14,17,10]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action90_valid : action90.Valid :=
  Action.check_sound _ (by decide +kernel)

def action91 : Action := ⟨![0,4,5,1,3,2],false,![9,2,7,5,3,8,6,1,0,4,15,19,18,13,11,16,14,12,17,10]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action91_valid : action91.Valid :=
  Action.check_sound _ (by decide +kernel)

def action92 : Action := ⟨![0,4,5,2,1,3],false,![9,5,2,7,6,3,8,0,4,1,18,15,19,11,16,13,12,17,14,10]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action92_valid : action92.Valid :=
  Action.check_sound _ (by decide +kernel)

def action93 : Action := ⟨![0,4,5,2,3,1],false,![9,5,7,2,6,8,3,4,0,1,18,19,15,16,11,13,17,12,14,10]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action93_valid : action93.Valid :=
  Action.check_sound _ (by decide +kernel)

def action94 : Action := ⟨![0,4,5,3,1,2],false,![9,7,2,5,8,3,6,1,4,0,19,15,18,13,16,11,14,17,12,10]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action94_valid : action94.Valid :=
  Action.check_sound _ (by decide +kernel)

def action95 : Action := ⟨![0,4,5,3,2,1],false,![9,7,5,2,8,6,3,4,1,0,19,18,15,16,13,11,17,14,12,10]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action95_valid : action95.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
