module
public import Paper2.Certificates.DihedralSupport.Data
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-! The finite certificate acts on the actual set of six-bit words. These
lemmas connect natural masks with arbitrary supports, without a finiteness
assumption on the coefficient field or any projective normalization. -/
@[expose] public section
namespace Paper2.Certificates.DihedralSupport
set_option maxHeartbeats 2000000

def packBits : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n+1, f => packBits n f ||| (if f n then 2^n else 0)

theorem testBit_packBits (n : Nat) (f : Nat → Bool) (i : Nat) :
    (packBits n f).testBit i = (decide (i < n) && f i) := by
  induction n with
  | zero => simp [packBits]
  | succ n ih =>
    simp only [packBits, Nat.testBit_or, ih]
    by_cases hi : i = n
    · subst i
      cases f n <;> simp
    · have hni : n ≠ i := Ne.symm hi
      have hh : (i < n+1) = (i < n) := propext (by omega)
      cases f n <;> simp [hni, hh]

theorem packBits_lt (n : Nat) (f : Nat → Bool) : packBits n f < 2^n := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  simp [testBit_packBits, Nat.not_lt.mpr hi]

def word6 (i : Nat) : Fin 6 → Bool := fun k => i.testBit (5-k.val)
def word4 (i : Nat) : Fin 4 → Bool := fun k => i.testBit (3-k.val)
def index6 (x : Fin 6 → Bool) : Nat :=
  32*(x 0).toNat + 16*(x 1).toNat + 8*(x 2).toNat +
  4*(x 3).toNat + 2*(x 4).toNat + (x 5).toNat

def index4 (x : Fin 4 → Bool) : Nat :=
  8*(x 0).toNat + 4*(x 1).toNat + 2*(x 2).toNat + (x 3).toNat

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem index6_word6 : ∀ i : Fin 64, index6 (word6 i.val) = i.val := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem word6_index6 : ∀ x : Fin 6 → Bool, word6 (index6 x) = x := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem index6_lt : ∀ x : Fin 6 → Bool, index6 x < 64 := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem index4_word4 : ∀ i : Fin 16, index4 (word4 i.val) = i.val := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem word4_index4 : ∀ x : Fin 4 → Bool, word4 (index4 x) = x := by decide +kernel
set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem index4_lt : ∀ x : Fin 4 → Bool, index4 x < 16 := by decide +kernel

def encodeSupport (S : (Fin 6 → Bool) → Bool) : Nat :=
  packBits 64 fun i => S (word6 i)

@[simp] theorem encodeSupport_spec (S : (Fin 6 → Bool) → Bool) (x : Fin 6 → Bool) :
    (encodeSupport S).testBit (index6 x) = S x := by
  simp [encodeSupport, testBit_packBits, index6_lt, word6_index6]

theorem encodeSupport_lt (S : (Fin 6 → Bool) → Bool) :
    encodeSupport S < 18446744073709551616 := packBits_lt 64 _

def pairPorts : Fin 15 → Fin 6 × Fin 6 :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),
    (2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]

def residualPorts : Fin 15 → Fin 4 → Fin 6 :=
  ![![2,3,4,5],![1,3,4,5],![1,2,4,5],![1,2,3,5],![1,2,3,4],
    ![0,3,4,5],![0,2,4,5],![0,2,3,5],![0,2,3,4],
    ![0,1,4,5],![0,1,3,5],![0,1,3,4],![0,1,2,5],![0,1,2,4],![0,1,2,3]]

/-- The two selected bits, followed by the unchanged increasing residual order. -/
def liftWord (p : Fin 15) (xi b : Bool) (y : Fin 4 → Bool) : Fin 6 → Bool :=
  fun k => if k = (pairPorts p).1 then b
    else if k = (pairPorts p).2 then b ^^ xi
    else if k = residualPorts p 0 then y 0
    else if k = residualPorts p 1 then y 1
    else if k = residualPorts p 2 then y 2
    else y 3

def liftIndex (p : Fin 15) (xi b : Bool) (r : Fin 16) : Nat :=
  index6 (liftWord p xi b (word4 r.val))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem liftWord_ports : ∀ (p : Fin 15) (xi b : Bool) (y : Fin 4 → Bool),
    liftWord p xi b y (pairPorts p).1 = b ∧
    liftWord p xi b y (pairPorts p).2 = b ^^ xi ∧
    ∀ k : Fin 4, liftWord p xi b y (residualPorts p k) = y k := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem liftWord_exhaustive : ∀ (p : Fin 15) (x : Fin 6 → Bool),
    liftWord p (x (pairPorts p).1 ^^ x (pairPorts p).2) (x (pairPorts p).1)
      (fun k => x (residualPorts p k)) = x := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem pairPorts_complete : ∀ i j : Fin 6, i < j → ∃ p, pairPorts p = (i,j) := by
  decide +kernel

def activeSources (cs : List Chunk) (r : Nat) : List Nat :=
  cs.filterMap fun c => if c.target ≤ r ∧ r-c.target < c.width
    then some (c.source + (r-c.target)) else none

theorem testBit_project_sources (cs : List Chunk) (m r : Nat) :
    (project cs m).testBit r = (activeSources cs r).any m.testBit := by
  rw [testBit_project]
  simp only [activeSources, List.any_filterMap]
  congr 1
  funext c
  by_cases hc : c.target ≤ r ∧ r-c.target < c.width
  · simp [hc.1, hc.2]
  · have hh : ¬ c.target ≤ r ∨ ¬ r-c.target < c.width := not_and_or.mp hc
    rcases hh with hh | hh <;> simp [hh]

def chunksFor (p : Fin 15) (xi : Bool) : List Chunk :=
  if xi then (pairChunks p).2 else (pairChunks p).1

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem projection_sources : ∀ (p : Fin 15) (xi : Bool) (r : Fin 16),
    activeSources (chunksFor p xi) r.val = [liftIndex p xi false r, liftIndex p xi true r] := by
  decide +kernel

/-- The executable projection is exactly the union of the two actual slices. -/
theorem projection_spec (p : Fin 15) (xi : Bool) (r : Fin 16) (m : Nat) :
    (project (chunksFor p xi) m).testBit r.val =
      (m.testBit (liftIndex p xi false r) || m.testBit (liftIndex p xi true r)) := by
  rw [testBit_project_sources, projection_sources]
  simp


end Paper2.Certificates.DihedralSupport
