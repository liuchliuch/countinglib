import Mathlib.Algebra.CharZero.Defs
import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.SplitIfs
import Lean.Elab.Tactic.Omega

/-! A sound, executable signed-equation elimination procedure.  The generated
DAG is only data; this module proves why each checked edge preserves every
solution over an arbitrary characteristic-zero integral domain. -/
namespace Paper2.Certificates.Q6.Coverage

inductive Term where
  | zero
  | pos (root : Fin 20)
  | neg (root : Fin 20)
  deriving DecidableEq, BEq, ReflBEq, LawfulBEq, Repr

abbrev State := Fin 20 → Term

variable {K : Type*} [CommRing K]

def Term.eval (p : Fin 20 → K) : Term → K
  | .zero => 0
  | .pos i => p i
  | .neg i => -p i

def Term.flip : Term → Term
  | .zero => .zero
  | .pos i => .neg i
  | .neg i => .pos i

@[simp] theorem Term.eval_flip (p : Fin 20 → K) (a : Term) :
    a.flip.eval p = -a.eval p := by cases a <;> simp [Term.flip, Term.eval]

def Term.subst (t : Term) (i : Fin 20) (v : Term) : Term :=
  match t with
  | .zero => .zero
  | .pos j => if j = i then v else .pos j
  | .neg j => if j = i then v.flip else .neg j

theorem Term.eval_subst (p : Fin 20 → K) (i : Fin 20) (v : Term)
    (h : p i = v.eval p) (t : Term) : (t.subst i v).eval p = t.eval p := by
  cases t with
  | zero => rfl
  | pos j => by_cases hj : j = i <;> simp [Term.subst, Term.eval, hj, h]
  | neg j => by_cases hj : j = i <;> cases v <;> simp_all [Term.subst, Term.eval, Term.flip]

/-- Eliminate the equation `eval a + eval b = 0`, keeping the least root.
An inconsistent signed cycle is recorded as a forced-zero component. -/
def eliminate (a b t : Term) : Term :=
  match a, b with
  | .zero, .zero => t
  | .zero, .pos j | .zero, .neg j => t.subst j .zero
  | .pos i, .zero | .neg i, .zero => t.subst i .zero
  | .pos i, .pos j | .neg i, .neg j =>
    if i = j then t.subst i .zero
    else if i < j then t.subst j (.neg i) else t.subst i (.neg j)
  | .pos i, .neg j | .neg i, .pos j =>
    if i = j then t
    else if i < j then t.subst j (.pos i) else t.subst i (.pos j)

variable [NoZeroDivisors K] [CharZero K]

private theorem self_add_zero {a : K} (h : a + a = 0) : a = 0 := by
  have hh : (2 : K) * a = 0 := by simpa [two_mul] using h
  exact (mul_eq_zero.mp hh).resolve_left (by norm_num)

/-- The sole place where characteristic two must be excluded: odd signed
cycles imply that their component vanishes. -/
theorem eliminate_sound (p : Fin 20 → K) (a b t : Term)
    (h : a.eval p + b.eval p = 0) : (eliminate a b t).eval p = t.eval p := by
  cases a with
  | zero =>
    cases b with
    | zero => rfl
    | pos j => exact Term.eval_subst p j .zero (by simpa [Term.eval] using h) t
    | neg j => exact Term.eval_subst p j .zero (by simpa [Term.eval] using h) t
  | pos i =>
    cases b with
    | zero => exact Term.eval_subst p i .zero (by simpa [Term.eval] using h) t
    | pos j =>
      simp only [eliminate]
      split_ifs with he hi
      · subst j
        exact Term.eval_subst p i .zero (self_add_zero h) t
      · apply Term.eval_subst
        simpa only [Term.eval] using (eq_neg_of_add_eq_zero_right h)
      · apply Term.eval_subst
        simpa only [Term.eval] using (eq_neg_of_add_eq_zero_left h)
    | neg j =>
      simp only [eliminate]
      split_ifs with he hi
      · rfl
      · apply Term.eval_subst
        simpa only [Term.eval] using (sub_eq_zero.mp (by simpa [Term.eval, sub_eq_add_neg] using h : p i - p j = 0)).symm
      · apply Term.eval_subst
        simpa only [Term.eval] using (sub_eq_zero.mp (by simpa [Term.eval, sub_eq_add_neg] using h : p i - p j = 0))
  | neg i =>
    cases b with
    | zero => exact Term.eval_subst p i .zero (by simpa [Term.eval] using h) t
    | pos j =>
      simp only [eliminate]
      split_ifs with he hi
      · rfl
      · apply Term.eval_subst
        simpa only [Term.eval] using (eq_of_sub_eq_zero (by simpa [Term.eval, sub_eq_add_neg, add_comm] using h : p j - p i = 0))
      · apply Term.eval_subst
        simpa only [Term.eval] using (eq_of_sub_eq_zero (by simpa [Term.eval, sub_eq_add_neg, add_comm] using h : p j - p i = 0)).symm
    | neg j =>
      have hp : p i + p j = 0 := by
        apply neg_eq_zero.mp
        rw [neg_add]
        exact h
      simp only [eliminate]
      split_ifs with he hi
      · subst j
        exact Term.eval_subst p i .zero (self_add_zero hp) t
      · apply Term.eval_subst
        simpa only [Term.eval] using (eq_neg_of_add_eq_zero_right hp)
      · apply Term.eval_subst
        simpa only [Term.eval] using (eq_neg_of_add_eq_zero_left hp)

/-- A state states actual coordinate relations, not just its dimension. -/
def Satisfies (q : Fin 20 → K) (s : State) : Prop :=
  ∀ i, q i = (s i).eval q

def addEdge (s : State) (u v : Fin 20) : State :=
  fun i => eliminate (s u) (s v) (s i)

theorem addEdge_sound (q : Fin 20 → K) (s : State) (u v : Fin 20)
    (hs : Satisfies q s) (he : q u + q v = 0) : Satisfies q (addEdge s u v) := by
  intro i
  rw [addEdge, eliminate_sound q (s u) (s v) (s i) (by rw [← hs u, ← hs v]; exact he)]
  exact hs i

abbrev Branch := (Fin 20 × Fin 20) × (Fin 20 × Fin 20)

def refine (s : State) (b : Branch) : State :=
  addEdge (addEdge s b.1.1 b.1.2) b.2.1 b.2.2

def Branch.Holds (q : Fin 20 → K) (b : Branch) : Prop :=
  q b.1.1 + q b.1.2 = 0 ∧ q b.2.1 + q b.2.2 = 0

theorem refine_sound (q : Fin 20 → K) (s : State) (b : Branch)
    (hs : Satisfies q s) (hb : b.Holds q) : Satisfies q (refine s b) :=
  addEdge_sound q _ _ _ (addEdge_sound q _ _ _ hs hb.1) hb.2

def initial : State := Term.pos

theorem satisfies_initial (q : Fin 20 → K) : Satisfies q initial := fun _ => rfl

/-- Kernel-friendly bounded checking, split into separately checked chunks. -/
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

theorem checkRange_add (f : Nat → Bool) (start m n : Nat) :
    checkRange f start (m+n) = (checkRange f start m && checkRange f (start+m) n) := by
  induction n with
  | zero => simp [checkRange]
  | succ n ih => simp [checkRange, ih, Nat.add_assoc, Bool.and_assoc]

theorem checkRange_join (f : Nat → Bool) (start m n : Nat)
    (hm : checkRange f start m = true)
    (hn : checkRange f (start+m) n = true) : checkRange f start (m+n) = true := by
  rw [checkRange_add, hm, hn]
  rfl

/-- All 60 coordinate equalities in one source-state transition. -/
def checkTransitionAt {m n : ℕ} (s : Fin m → State) (t : Fin n → State)
    (next : Fin m → Fin 3 → Fin n) (opts : Fin 3 → Branch) (i : Nat) : Bool :=
  if hi : i < m then
    (List.finRange 3).all fun b => (List.finRange 20).all fun k =>
      (refine (s ⟨i, hi⟩) (opts b) k == t (next ⟨i, hi⟩ b) k)
  else true

def checkTransition {m n : ℕ} (s : Fin m → State) (t : Fin n → State)
    (next : Fin m → Fin 3 → Fin n) (opts : Fin 3 → Branch) : Bool :=
  checkRange (checkTransitionAt s t next opts) 0 m

theorem checkTransition_sound {m n : ℕ} (s : Fin m → State) (t : Fin n → State)
    (next : Fin m → Fin 3 → Fin n) (opts : Fin 3 → Branch)
    (h : checkTransition s t next opts = true) (i : Fin m) (b : Fin 3) :
    refine (s i) (opts b) = t (next i b) := by
  funext k
  have hi := checkRange_sound _ 0 m h i.val (Nat.zero_le _) (by simpa using i.isLt)
  simp only [checkTransitionAt, dif_pos i.isLt] at hi
  have hb := List.all_eq_true.mp hi b (by simp)
  have hk := List.all_eq_true.mp hb k (by simp)
  exact beq_iff_eq.mp hk

def Covered {n : ℕ} (q : Fin 20 → K) (s : Fin n → State) : Prop :=
  ∃ i, Satisfies q (s i)

theorem covered_step {m n : ℕ} (q : Fin 20 → K)
    (s : Fin m → State) (t : Fin n → State)
    (next : Fin m → Fin 3 → Fin n) (opts : Fin 3 → Branch)
    (h : ∀ i b, refine (s i) (opts b) = t (next i b))
    (hs : Covered q s) (hb : ∃ b, (opts b).Holds q) : Covered q t := by
  obtain ⟨i, hi⟩ := hs
  obtain ⟨b, hb⟩ := hb
  refine ⟨next i b, ?_⟩
  rw [← h i b]
  exact refine_sound q _ _ hi hb

end Paper2.Certificates.Q6.Coverage
