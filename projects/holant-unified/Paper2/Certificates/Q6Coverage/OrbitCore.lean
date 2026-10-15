import Paper2.Certificates.Q6Coverage.Core
import Mathlib.Data.Fintype.EquivFin

namespace Paper2.Certificates.Q6.Coverage

/-- Authoritative Python lexicographic triple order; port k is bit k. -/
def coordinateMasks : Fin 20 → Nat :=
  ![7,11,19,35,13,21,37,25,41,49,14,22,38,26,42,50,28,44,52,56]

def permuteMask (p : Fin 6 → Fin 6) (m : Nat) : Nat :=
  ((List.finRange 6).map fun k => if m.testBit k.val then 2^(p k).val else 0).sum

def actedMask (p : Fin 6 → Fin 6) (complement : Bool) (m : Nat) : Nat :=
  let v := permuteMask p m
  if complement then v ^^^ 63 else v

/-- A labelled S6/complement transformation, with its complete coordinate map. -/
structure Action where
  ports : Fin 6 → Fin 6
  complement : Bool
  coords : Fin 20 → Fin 20

/-- Both bijections and every bitmask correspondence are verified. -/
def Action.Valid (a : Action) : Prop :=
  Function.Bijective a.ports ∧ Function.Bijective a.coords ∧
    ∀ i, coordinateMasks (a.coords i) = actedMask a.ports a.complement (coordinateMasks i)

def checkInjective {n : Nat} (f : Fin n → Fin n) : Bool :=
  (List.finRange n).all fun i => (List.finRange n).all fun j =>
    (!(f i == f j)) || (i == j)

theorem checkInjective_sound {n : Nat} (f : Fin n → Fin n)
    (h : checkInjective f = true) : Function.Bijective f := by
  apply (Fintype.bijective_iff_injective_and_card f).mpr
  refine ⟨?_, rfl⟩
  intro i j hij
  have hi := List.all_eq_true.mp h i (by simp)
  have hj := List.all_eq_true.mp hi j (by simp)
  simpa [hij] using hj

def Action.check (a : Action) : Bool :=
  checkInjective a.ports && checkInjective a.coords &&
    (List.finRange 20).all fun i =>
      coordinateMasks (a.coords i) == actedMask a.ports a.complement (coordinateMasks i)

theorem Action.check_sound (a : Action) (h : a.check = true) : a.Valid := by
  have hh := Bool.and_eq_true_iff.mp h
  obtain ⟨hp, hc⟩ := Bool.and_eq_true_iff.mp hh.1
  have hm := hh.2
  refine ⟨checkInjective_sound _ hp, checkInjective_sound _ hc, ?_⟩
  intro i
  exact beq_iff_eq.mp (List.all_eq_true.mp hm i (by simp))

/-- Reparameterize a signed row; zero and signs are retained exactly. -/
def Term.bind (parameters : Fin 20 → Term) : Term → Term
  | .zero => .zero
  | .pos i => parameters i
  | .neg i => (parameters i).flip

variable {K : Type*} [CommRing K]

theorem Term.eval_bind (parameters : Fin 20 → Term) (q : Fin 20 → K) (t : Term) :
    (Term.bind parameters t).eval q = t.eval (fun i => (parameters i).eval q) := by
  cases t with
  | zero => rfl
  | pos i => rfl
  | neg i => exact Term.eval_flip q (parameters i)

structure OrbitWitness where
  row : Fin 24
  action : Action
  parameters : Fin 20 → Term
  valid : action.Valid

def OrbitWitness.Checks (rows : Fin 24 → State) (s : State) (w : OrbitWitness) : Prop :=
  w.action.Valid ∧ ∀ i, s (w.action.coords i) = Term.bind w.parameters (rows w.row i)

def checkOrbit (rows : Fin 24 → State) (s : State) (w : OrbitWitness) : Bool :=
  (List.finRange 20).all fun i =>
    s (w.action.coords i) == Term.bind w.parameters (rows w.row i)

theorem checkOrbit_sound (rows : Fin 24 → State) (s : State) (w : OrbitWitness)
    (h : checkOrbit rows s w = true) : w.Checks rows s := by
  refine ⟨w.valid, ?_⟩
  intro i
  exact beq_iff_eq.mp (List.all_eq_true.mp h i (by simp))

/-- Explicit orbit membership, including all twenty coefficient equalities. -/
def InOrbits (rows : Fin 24 → State) (q : Fin 20 → K) : Prop :=
  ∃ (r : Fin 24) (a : Action) (p : Fin 20 → K),
    a.Valid ∧ ∀ i, q (a.coords i) = (rows r i).eval p

theorem orbitWitness_sound (rows : Fin 24 → State) (q : Fin 20 → K)
    (s : State) (w : OrbitWitness) (hw : w.Checks rows s) (hs : Satisfies q s) :
    InOrbits rows q := by
  refine ⟨w.row, w.action, fun i => (w.parameters i).eval q, hw.1, ?_⟩
  intro i
  rw [hs, hw.2 i, Term.eval_bind]

end Paper2.Certificates.Q6.Coverage
