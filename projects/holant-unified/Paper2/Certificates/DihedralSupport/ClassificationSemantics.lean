module
public import Paper2.Certificates.DihedralSupport.Semantics
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Finset.Basic

/-! Literal support geometry for the six-port certificate.  The finite
certificate predicates are related to arbitrary Boolean supports and to the
union of the two actual slices, before any enumeration result is used. -/
@[expose] public section
namespace Paper2.Certificates.DihedralSupport

abbrev Support6 := (Fin 6 → Bool) → Bool
abbrev Support4 := (Fin 4 → Bool) → Bool

theorem encodeSupport_injective : Function.Injective encodeSupport := by
  intro S T h
  funext x
  simpa only [encodeSupport_spec] using congrArg (fun m => m.testBit (index6 x)) h

theorem encodeSupport_decode (m : Nat) (hm : m < 18446744073709551616) :
    encodeSupport (fun x => m.testBit (index6 x)) = m := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 64
  · simpa [encodeSupport, testBit_packBits, hi] using
      congrArg m.testBit (index6_word6 ⟨i,hi⟩)
  · have h64 : m < 2^64 := hm
    have hii : 64 ≤ i := by omega
    have hp : 2^64 ≤ 2^i := Nat.pow_le_pow_right (by decide) hii
    have hm' : m < 2^i := lt_of_lt_of_le h64 hp
    simp [encodeSupport, testBit_packBits, hi, Nat.testBit_eq_false_of_lt hm']

def complement4 (x : Fin 4 → Bool) : Fin 4 → Bool := fun k => !(x k)
def parity4 (x : Fin 4 → Bool) : Bool := x 0 ^^ x 1 ^^ x 2 ^^ x 3

def encodeSupport4 (U : Support4) : Nat := packBits 16 fun i => U (word4 i)

@[simp] theorem encodeSupport4_spec (U : Support4) (x : Fin 4 → Bool) :
    (encodeSupport4 U).testBit (index4 x) = U x := by
  simp [encodeSupport4, testBit_packBits, index4_lt, word4_index4]

theorem encodeSupport4_lt (U : Support4) : encodeSupport4 U < 65536 :=
  packBits_lt 16 _

theorem encodeSupport4_injective : Function.Injective encodeSupport4 := by
  intro U V h
  funext x
  simpa only [encodeSupport4_spec] using congrArg (fun m => m.testBit (index4 x)) h

def complementBlocks (a b : Fin 4 → Bool) : Support4 :=
  fun x => decide (x = a ∨ x = complement4 a ∨ x = b ∨ x = complement4 b)

/-- Empty, or one or two complete complement blocks of one parity.  The
one-block case is included by taking the two representatives equal. -/
def AllowedProjection (U : Support4) : Prop :=
  U = (fun _ => false) ∨
    ∃ a b, parity4 a = parity4 b ∧ U = complementBlocks a b

def complementBlockMasks : List Nat :=
  0 :: (List.finRange 16).flatMap (fun a =>
    ((List.finRange 16).filter (fun b => parity4 (word4 a.val) == parity4 (word4 b.val))).map
      (fun b => encodeSupport4 (complementBlocks (word4 a.val) (word4 b.val))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem complementBlockMasks_exact :
    complementBlockMasks.toFinset = allowedUnions.toFinset := by decide +kernel

theorem allowedProjection_iff_mask (U : Support4) :
    AllowedProjection U ↔ encodeSupport4 U ∈ allowedUnions := by
  rw [← List.mem_toFinset, ← complementBlockMasks_exact, List.mem_toFinset]
  constructor
  · rintro (rfl | ⟨a, b, hp, rfl⟩)
    · simp [complementBlockMasks, encodeSupport4, packBits]
    · apply List.mem_cons_of_mem
      apply List.mem_flatMap.mpr
      refine ⟨⟨index4 a, index4_lt a⟩, List.mem_finRange _, ?_⟩
      apply List.mem_map.mpr
      refine ⟨⟨index4 b, index4_lt b⟩, ?_, ?_⟩
      · simp [word4_index4, hp]
      · simp [word4_index4]
  · intro h
    rcases List.mem_cons.mp h with h | h
    · left
      apply encodeSupport4_injective
      simpa [encodeSupport4, packBits] using h
    · rcases List.mem_flatMap.mp h with ⟨a, _, h⟩
      rcases List.mem_map.mp h with ⟨b, hb, he⟩
      refine Or.inr ⟨word4 a.val, word4 b.val, ?_, ?_⟩
      · simpa using (List.mem_filter.mp hb).2
      · exact encodeSupport4_injective he.symm

/-- The source's support union at the selected xor, in increasing residual
port order. -/
def projectionSupport (S : Support6) (p : Fin 15) (xi : Bool) : Support4 :=
  fun y => S (liftWord p xi false y) || S (liftWord p xi true y)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem chunksFor_bound_check : ∀ (p : Fin 15) (xi : Bool),
    (chunksFor p xi).all (fun c => decide (c.target + c.width ≤ 16)) = true := by
  decide +kernel

theorem chunksFor_bound (p : Fin 15) (xi : Bool) (c : Chunk)
    (hc : c ∈ chunksFor p xi) : c.target + c.width ≤ 16 :=
  of_decide_eq_true ((List.all_eq_true.mp (chunksFor_bound_check p xi)) c hc)

theorem project_bound (p : Fin 15) (xi : Bool) (m : Nat) :
    project (chunksFor p xi) m < 65536 := by
  change project (chunksFor p xi) m < 2^16
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [testBit_project]
  apply List.any_eq_false.mpr
  intro c hc
  have hbound := chunksFor_bound p xi c hc
  by_cases hci : c.target ≤ i
  · have hn : ¬ i - c.target < c.width := by omega
    simp [hn]
  · simp [hci]

theorem projection_encode (S : Support6) (p : Fin 15) (xi : Bool) :
    project (chunksFor p xi) (encodeSupport S) =
      encodeSupport4 (projectionSupport S p xi) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 16
  · have hp := projection_spec p xi ⟨i, hi⟩ (encodeSupport S)
    simpa [liftIndex, projectionSupport, encodeSupport4, testBit_packBits, hi] using hp
  · have h16 : project (chunksFor p xi) (encodeSupport S) < 2^16 := project_bound p xi _
    have hii : 16 ≤ i := by omega
    have hp : 2^16 ≤ 2^i := Nat.pow_le_pow_right (by decide) hii
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le h16 hp)]
    simp [encodeSupport4, testBit_packBits, hi]

def AdmissibleMask (m : Nat) : Prop :=
  m < 18446744073709551616 ∧
    ∀ p : Fin 15, ∀ xi : Bool, project (chunksFor p xi) m ∈ allowedUnions

def AdmissibleSupport (S : Support6) : Prop :=
  ∀ p : Fin 15, ∀ xi : Bool, AllowedProjection (projectionSupport S p xi)

theorem admissibleSupport_iff_mask (S : Support6) :
    AdmissibleSupport S ↔ AdmissibleMask (encodeSupport S) := by
  constructor
  · intro h
    refine ⟨encodeSupport_lt S, ?_⟩
    intro p xi
    rw [projection_encode]
    exact (allowedProjection_iff_mask _).mp (h p xi)
  · rintro ⟨_, h⟩ p xi
    apply (allowedProjection_iff_mask _).mpr
    rw [← projection_encode]
    exact h p xi

theorem admissible_goodAt {m : Nat} (h : AdmissibleMask m) (p : Fin 15) :
    goodAt p m = true := by
  have h0 := h.2 p false
  have h1 := h.2 p true
  simpa [goodAt, pairGood, chunksFor] using
    Bool.and_eq_true_iff.mpr ⟨List.contains_iff_mem.mpr h0, List.contains_iff_mem.mpr h1⟩

theorem all_goodAt_goodAll {m : Nat} (h : ∀ p : Fin 15, goodAt p m = true) :
    goodAll m = true := by
  have h1 : pairGood chunks1_0 chunks1_1 m = true := h 1
  have h2 : pairGood chunks2_0 chunks2_1 m = true := h 2
  have h3 : pairGood chunks3_0 chunks3_1 m = true := h 3
  have h4 : pairGood chunks4_0 chunks4_1 m = true := h 4
  have h5 : pairGood chunks5_0 chunks5_1 m = true := h 5
  have h6 : pairGood chunks6_0 chunks6_1 m = true := h 6
  have h7 : pairGood chunks7_0 chunks7_1 m = true := h 7
  have h8 : pairGood chunks8_0 chunks8_1 m = true := h 8
  have h9 : pairGood chunks9_0 chunks9_1 m = true := h 9
  have h10 : pairGood chunks10_0 chunks10_1 m = true := h 10
  have h11 : pairGood chunks11_0 chunks11_1 m = true := h 11
  have h12 : pairGood chunks12_0 chunks12_1 m = true := h 12
  have h13 : pairGood chunks13_0 chunks13_1 m = true := h 13
  have h14 : pairGood chunks14_0 chunks14_1 m = true := h 14
  simp only [goodAll, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, Bool.and_self]

end Paper2.Certificates.DihedralSupport
