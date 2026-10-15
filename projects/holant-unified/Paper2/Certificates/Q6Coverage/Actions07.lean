import Paper2.Certificates.Q6Coverage.Actions06

namespace Paper2.Certificates.Q6.Coverage

def action112 : Action := ⟨![0,5,3,4,1,2],false,![8,9,3,6,7,1,4,2,5,0,19,14,17,15,18,12,13,16,10,11]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action112_valid : action112.Valid :=
  Action.check_sound _ (by decide +kernel)

def action113 : Action := ⟨![0,5,3,4,2,1],false,![8,9,6,3,7,4,1,5,2,0,19,17,14,18,15,12,16,13,10,11]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action113_valid : action113.Valid :=
  Action.check_sound _ (by decide +kernel)

def action114 : Action := ⟨![0,5,4,1,2,3],false,![9,3,6,8,2,5,7,0,1,4,15,18,19,12,14,17,11,13,16,10]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action114_valid : action114.Valid :=
  Action.check_sound _ (by decide +kernel)

def action115 : Action := ⟨![0,5,4,1,3,2],false,![9,3,8,6,2,7,5,1,0,4,15,19,18,14,12,17,13,11,16,10]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action115_valid : action115.Valid :=
  Action.check_sound _ (by decide +kernel)

def action116 : Action := ⟨![0,5,4,2,1,3],false,![9,6,3,8,5,2,7,0,4,1,18,15,19,12,17,14,11,16,13,10]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action116_valid : action116.Valid :=
  Action.check_sound _ (by decide +kernel)

def action117 : Action := ⟨![0,5,4,2,3,1],false,![9,6,8,3,5,7,2,4,0,1,18,19,15,17,12,14,16,11,13,10]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action117_valid : action117.Valid :=
  Action.check_sound _ (by decide +kernel)

def action118 : Action := ⟨![0,5,4,3,1,2],false,![9,8,3,6,7,2,5,1,4,0,19,15,18,14,17,12,13,16,11,10]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action118_valid : action118.Valid :=
  Action.check_sound _ (by decide +kernel)

def action119 : Action := ⟨![0,5,4,3,2,1],false,![9,8,6,3,7,5,2,4,1,0,19,18,15,17,14,12,16,13,11,10]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action119_valid : action119.Valid :=
  Action.check_sound _ (by decide +kernel)

def action120 : Action := ⟨![1,0,2,3,4,5],false,![0,1,2,3,10,11,12,13,14,15,4,5,6,7,8,9,16,17,18,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action120_valid : action120.Valid :=
  Action.check_sound _ (by decide +kernel)

def action121 : Action := ⟨![1,0,2,3,5,4],false,![0,1,3,2,10,12,11,14,13,15,4,6,5,8,7,9,17,16,18,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action121_valid : action121.Valid :=
  Action.check_sound _ (by decide +kernel)

def action122 : Action := ⟨![1,0,2,4,3,5],false,![0,2,1,3,11,10,12,13,15,14,5,4,6,7,9,8,16,18,17,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action122_valid : action122.Valid :=
  Action.check_sound _ (by decide +kernel)

def action123 : Action := ⟨![1,0,2,4,5,3],false,![0,2,3,1,11,12,10,15,13,14,5,6,4,9,7,8,18,16,17,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action123_valid : action123.Valid :=
  Action.check_sound _ (by decide +kernel)

def action124 : Action := ⟨![1,0,2,5,3,4],false,![0,3,1,2,12,10,11,14,15,13,6,4,5,8,9,7,17,18,16,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action124_valid : action124.Valid :=
  Action.check_sound _ (by decide +kernel)

def action125 : Action := ⟨![1,0,2,5,4,3],false,![0,3,2,1,12,11,10,15,14,13,6,5,4,9,8,7,18,17,16,19]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action125_valid : action125.Valid :=
  Action.check_sound _ (by decide +kernel)

def action126 : Action := ⟨![1,0,3,2,4,5],false,![1,0,2,3,10,13,14,11,12,15,4,7,8,5,6,9,16,17,19,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action126_valid : action126.Valid :=
  Action.check_sound _ (by decide +kernel)

def action127 : Action := ⟨![1,0,3,2,5,4],false,![1,0,3,2,10,14,13,12,11,15,4,8,7,6,5,9,17,16,19,18]⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem action127_valid : action127.Valid :=
  Action.check_sound _ (by decide +kernel)

end Paper2.Certificates.Q6.Coverage
