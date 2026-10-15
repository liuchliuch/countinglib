import Counting.Algorithm.VariableElimination.Enumeration
import Counting.Algorithm.VariableElimination.BlockIndex
import Mathlib.Data.List.FinRange
import Mathlib.Tactic.Ring

/-!
# Direct assignment addresses

The first enumerated coordinate is most significant. The executable address is
an ordinary Horner fold; the recursive positional expression is used for proofs.
-/

namespace Counting.Algorithm.VariableElimination

universe u v

/-- An executable most-significant-first address, with a supplied digit map. -/
def hornerIndex {α : Type u} (q : Nat) (digit : α → Nat) (xs : List α) : Nat :=
  xs.foldl (fun acc x => acc * q + digit x) 0

/-- Positional expression for the same address. -/
def radixIndex {α : Type u} (q : Nat) (digit : α → Nat) : List α → Nat
  | [] => 0
  | x :: xs => digit x * q ^ xs.length + radixIndex q digit xs

theorem foldl_horner_eq {α : Type u} (q : Nat) (digit : α → Nat)
    (xs : List α) (acc : Nat) :
    xs.foldl (fun acc x => acc * q + digit x) acc =
      acc * q ^ xs.length + radixIndex q digit xs := by
  induction xs generalizing acc with
  | nil => simp [radixIndex]
  | cons x xs ih =>
      simp only [List.foldl_cons, List.length_cons, radixIndex, ih, Nat.pow_succ]
      ring

theorem hornerIndex_eq_radixIndex {α : Type u} (q : Nat) (digit : α → Nat)
    (xs : List α) : hornerIndex q digit xs = radixIndex q digit xs := by
  simp [hornerIndex, foldl_horner_eq]

theorem radixIndex_lt {α : Type u} (q : Nat) (digit : α → Nat)
    (xs : List α) (h : ∀ x ∈ xs, digit x < q) :
    radixIndex q digit xs < q ^ xs.length := by
  induction xs with
  | nil => simp [radixIndex]
  | cons x xs ih =>
      have hx := h x (by simp)
      have ht := ih (fun y hy => h y (by simp [hy]))
      simp only [radixIndex, List.length_cons, Nat.pow_succ]
      calc
        digit x * q ^ xs.length + radixIndex q digit xs <
            digit x * q ^ xs.length + q ^ xs.length := Nat.add_lt_add_left ht _
        _ = (digit x + 1) * q ^ xs.length := by ring
        _ ≤ q * q ^ xs.length := Nat.mul_le_mul_right _ hx
        _ = q ^ xs.length * q := Nat.mul_comm _ _

theorem hornerIndex_lt {α : Type u} (q : Nat) (digit : α → Nat)
    (xs : List α) (h : ∀ x ∈ xs, digit x < q) :
    hornerIndex q digit xs < q ^ xs.length := by
  rw [hornerIndex_eq_radixIndex]
  exact radixIndex_lt q digit xs h

/-- Address in the existing sorted Cartesian-product table layout. Only the
coordinate and colour lists are enumerated; no list of assignments is built. -/
def assignmentIndex {α : Type u} {D : Type v}
    [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D] (a : α → D) : Nat :=
  let xs := enumerateValues α
  let ds := enumerateValues D
  hornerIndex ds.length (fun x => ds.idxOf (a x)) xs

theorem assignmentIndex_lt {α : Type u} {D : Type v}
    [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D] (a : α → D) :
    assignmentIndex a < Fintype.card D ^ Fintype.card α := by
  simpa only [assignmentIndex, length_enumerateValues] using
    hornerIndex_lt (enumerateValues D).length
      (fun x => (enumerateValues D).idxOf (a x)) (enumerateValues α)
      (fun x _ => List.idxOf_lt_length_of_mem (mem_enumerateValues (a x)))


/-- The list product has a common radix even for radix zero or one. -/
theorem length_pi_uniform {α : Type u} {D : Type v} [DecidableEq α]
    (xs : List α) (ds : List D) :
    (List.pi xs (fun _ => ds)).length = ds.length ^ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [List.pi_cons, List.length_flatMap, ih, Nat.pow_succ,
      Nat.mul_comm]

theorem radixIndex_pi_lt {α : Type u} {D : Type v}
    [DecidableEq α] [DecidableEq D] (xs : List α) (ds : List D)
    (a : α → D) (h : ∀ x ∈ xs, a x ∈ ds) :
    radixIndex ds.length (fun x => ds.idxOf (a x)) xs <
      (List.pi xs (fun _ => ds)).length := by
  rw [length_pi_uniform]
  exact radixIndex_lt _ _ _ (fun x hx => List.idxOf_lt_length_of_mem (h x hx))

/-- A most-significant-first address selects the corresponding dependent
assignment from the executable Cartesian product. -/
theorem getElem_pi_radixIndex {α : Type u} {D : Type v}
    [DecidableEq α] [DecidableEq D] (xs : List α) (ds : List D)
    (a : α → D) (h : ∀ x ∈ xs, a x ∈ ds) :
    (List.pi xs (fun _ => ds))[radixIndex ds.length (fun x => ds.idxOf (a x)) xs]'
        (radixIndex_pi_lt xs ds a h) = (fun x _ => a x) := by
  induction xs with
  | nil =>
      funext x hx
      simp at hx
  | cons x xs ih =>
      have hx : ds.idxOf (a x) < ds.length :=
        List.idxOf_lt_length_of_mem (h x (by simp))
      have ht : ∀ y ∈ xs, a y ∈ ds := fun y hy => h y (by simp [hy])
      have hj : radixIndex ds.length (fun y => ds.idxOf (a y)) xs <
          ds.length ^ xs.length :=
        radixIndex_lt _ _ _ (fun y hy => List.idxOf_lt_length_of_mem (ht y hy))
      simp only [List.pi_cons, radixIndex]
      rw [getElem_flatMap_const ds
        (fun d => (List.pi xs (fun _ => ds)).map (List.Pi.cons x xs d))
        (ds.length ^ xs.length)
        (fun d _ => by simp [length_pi_uniform])
        (ds.idxOf (a x)) (radixIndex ds.length (fun y => ds.idxOf (a y)) xs) hx hj]
      rw [List.getElem_map, List.getElem_idxOf hx, ih ht]
      exact List.Pi.cons_eta (fun y (_ : y ∈ x :: xs) => a y)

/-- Direct addressing retrieves the original assignment in the existing layout. -/
theorem getElem_enumerateAssignments_assignmentIndex {α : Type u} {D : Type v}
    [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D] (a : α → D) :
    (enumerateAssignments α D)[assignmentIndex a]'
        (by rw [length_enumerateAssignments]; exact assignmentIndex_lt a) = a := by
  simp only [assignmentIndex, hornerIndex_eq_radixIndex,
    enumerateAssignments, List.getElem_map]
  rw [getElem_pi_radixIndex _ _ a (fun x _ => mem_enumerateValues (a x))]

/-- The address is exactly the former linear-search index, including radix zero
and one and the unique assignment on an empty coordinate type. -/
theorem idxOf_enumerateAssignments_eq_assignmentIndex {α : Type u} {D : Type v}
    [Fintype α] [LinearOrder α] [Fintype D] [LinearOrder D] (a : α → D) :
    (enumerateAssignments α D).idxOf a = assignmentIndex a := by
  have h : assignmentIndex a < (enumerateAssignments α D).length := by
    rw [length_enumerateAssignments]
    exact assignmentIndex_lt a
  have hn := (nodup_enumerateAssignments α D).idxOf_getElem (assignmentIndex a) h
  rwa [getElem_enumerateAssignments_assignmentIndex] at hn

/-- Finite colours have their digit in their value, so this address performs no
colour-list search. -/
def assignmentIndexFin {α : Type u} [Fintype α] [LinearOrder α]
    (q : Nat) (a : α → Fin q) : Nat :=
  hornerIndex q (fun x => (a x).val) (enumerateValues α)

theorem assignmentIndexFin_lt {α : Type u} [Fintype α] [LinearOrder α]
    (q : Nat) (a : α → Fin q) : assignmentIndexFin q a < q ^ Fintype.card α := by
  simpa only [assignmentIndexFin, length_enumerateValues] using
    hornerIndex_lt q (fun x => (a x).val) (enumerateValues α) (fun x _ => (a x).isLt)

@[simp] theorem enumerateValues_fin (q : Nat) :
    enumerateValues (Fin q) = List.finRange q := Fin.sort_univ q

@[simp] theorem idxOf_enumerateValues_fin (q : Nat) (d : Fin q) :
    (enumerateValues (Fin q)).idxOf d = d.val := by
  rw [enumerateValues_fin]
  exact List.idxOf_finRange d

theorem assignmentIndexFin_eq_assignmentIndex {α : Type u} [Fintype α] [LinearOrder α]
    (q : Nat) (a : α → Fin q) : assignmentIndexFin q a = assignmentIndex a := by
  simp [assignmentIndexFin, assignmentIndex]

end Counting.Algorithm.VariableElimination
