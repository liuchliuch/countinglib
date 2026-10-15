module
public import Mathlib.Data.Nat.Bitwise
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fin.VecNotation
public import Lean.Elab.Tactic.Omega

/-! Exact six-port support masks, independent of scalar coefficients.
The recursive local list enumerates all nonempty lift choices over each
residual support word. All coverage arguments are theorems of Lean. -/
@[expose] public section
namespace Paper2.Certificates.DihedralSupport

/-- All pairs of bounded masks whose bitwise union is the given mask. -/
def placements : Nat → Nat → List (Nat × Nat)
  | 0, _ => [(0, 0)]
  | n+1, u =>
    if u % 2 = 0 then
      (placements n (u / 2)).map fun p => (2 * p.1, 2 * p.2)
    else
      (placements n (u / 2)).flatMap fun p =>
        [(2 * p.1 + 1, 2 * p.2), (2 * p.1, 2 * p.2 + 1),
          (2 * p.1 + 1, 2 * p.2 + 1)]

private theorem or_div_two (a b : Nat) : (a ||| b) / 2 = (a / 2) ||| (b / 2) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_div_two, Nat.testBit_or]

/-- Universal local completeness; it does not enumerate the `2^32` possible
pairs and it does not assume that the actual support was generated. -/
theorem mem_placements (n a b : Nat) (ha : a < 2^n) (hb : b < 2^n) :
    (a, b) ∈ placements n (a ||| b) := by
  induction n generalizing a b with
  | zero =>
    have : a = 0 := by simpa using ha
    have : b = 0 := by simpa using hb
    subst a; subst b; simp [placements]
  | succ n ih =>
    have ha' : a / 2 < 2^n := by
      have hpow : 2^(n+1) = 2^n * 2 := Nat.pow_succ ..
      rw [hpow] at ha
      omega
    have hb' : b / 2 < 2^n := by
      have hpow : 2^(n+1) = 2^n * 2 := Nat.pow_succ ..
      rw [hpow] at hb
      omega
    have htail := ih (a/2) (b/2) ha' hb'
    rw [placements, or_div_two]
    rcases Nat.mod_two_eq_zero_or_one a with ha0 | ha1 <;>
      rcases Nat.mod_two_eq_zero_or_one b with hb0 | hb1
    · have hu : (a ||| b) % 2 = 0 := by
        have hh := Nat.or_mod_two_eq_one (a := a) (b := b)
        have hm := Nat.mod_two_eq_zero_or_one (a ||| b)
        omega
      rw [if_pos hu]
      apply List.mem_map.mpr
      refine ⟨(a/2, b/2), htail, ?_⟩
      apply Prod.ext <;> dsimp <;> omega
    · have hu : (a ||| b) % 2 ≠ 0 := by
        have hh := (Nat.or_mod_two_eq_one (a := a) (b := b)).mpr (Or.inr hb1)
        omega
      rw [if_neg hu]
      apply List.mem_flatMap.mpr
      refine ⟨(a/2, b/2), htail, ?_⟩
      have he : (a,b) = (2*(a/2), 2*(b/2)+1) := by apply Prod.ext <;> dsimp <;> omega
      simp [he]
    · have hu : (a ||| b) % 2 ≠ 0 := by
        have hh := (Nat.or_mod_two_eq_one (a := a) (b := b)).mpr (Or.inl ha1)
        omega
      rw [if_neg hu]
      apply List.mem_flatMap.mpr
      refine ⟨(a/2, b/2), htail, ?_⟩
      have he : (a,b) = (2*(a/2)+1, 2*(b/2)) := by apply Prod.ext <;> dsimp <;> omega
      simp [he]
    · have hu : (a ||| b) % 2 ≠ 0 := by
        have hh := (Nat.or_mod_two_eq_one (a := a) (b := b)).mpr (Or.inl ha1)
        omega
      rw [if_neg hu]
      apply List.mem_flatMap.mpr
      refine ⟨(a/2, b/2), htail, ?_⟩
      have he : (a,b) = (2*(a/2)+1, 2*(b/2)+1) := by apply Prod.ext <;> dsimp <;> omega
      simp [he]

/-- The displayed twenty allowed nonempty four-bit support masks, plus zero.
Their coordinatewise interpretation is proved separately. -/
def allowedUnions : List Nat :=
  [0,384,576,1056,1632,2064,2448,4104,4680,5160,8196,8580,10260,
   16386,16770,18450,24582,32769,33345,33825,36873]

def localChoices : List (Nat × Nat) :=
  allowedUnions.flatMap (placements 16)

theorem mem_localChoices (a b : Nat) (ha : a < 65536) (hb : b < 65536)
    (hu : a ||| b ∈ allowedUnions) : (a,b) ∈ localChoices := by
  exact List.mem_flatMap.mpr ⟨a ||| b, hu, mem_placements 16 a b ha hb⟩

/-- Four consecutive sixteen-bit slices in lexicographic word order. -/
def assemble (equal mixed : Nat × Nat) : Nat :=
  equal.1 + (mixed.1 <<< 16) + (mixed.2 <<< 32) + (equal.2 <<< 48)

structure Chunk where
  source : Nat
  target : Nat
  width : Nat
  deriving Repr, DecidableEq

def Chunk.copy (c : Chunk) (m : Nat) : Nat :=
  ((m >>> c.source) % (2^c.width)) <<< c.target

def project (cs : List Chunk) (m : Nat) : Nat :=
  cs.foldr (fun c out => c.copy m ||| out) 0

/-- All the surviving masks are actually checked against this predicate. -/
def pairGood (equal mixed : List Chunk) (m : Nat) : Bool :=
  allowedUnions.contains (project equal m) && allowedUnions.contains (project mixed m)

/-- Chunks contain only exact integer shifts, masks, and unions. -/
theorem testBit_project (cs : List Chunk) (m r : Nat) :
    (project cs m).testBit r = cs.any (fun c =>
      decide (c.target ≤ r) && decide (r-c.target < c.width) &&
        m.testBit (c.source + (r-c.target))) := by
  induction cs with
  | nil => simp [project]
  | cons c cs ih =>
    simp only [project, List.foldr_cons, Nat.testBit_or] at *
    rw [ih]
    simp only [List.any_cons, Chunk.copy, Nat.testBit_shiftLeft,
      Nat.testBit_mod_two_pow, Nat.testBit_shiftRight]
    simp only [Bool.and_assoc]

/-- Kernel-friendly bounded checking, independently of any other certificate. -/
def checkRange (f : Nat → Bool) (start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => checkRange f start n && f (start+n)

theorem checkRange_sound (f : Nat → Bool) (start len : Nat)
    (h : checkRange f start len = true) (i : Nat)
    (hlo : start ≤ i) (hhi : i < start+len) : f i = true := by
  induction len with
  | zero => omega
  | succ n ih =>
    obtain ⟨hp, hn⟩ := Bool.and_eq_true_iff.mp h
    by_cases he : i = start+n
    · simpa [he] using hn
    · exact ih hp (by omega)

end Paper2.Certificates.DihedralSupport
