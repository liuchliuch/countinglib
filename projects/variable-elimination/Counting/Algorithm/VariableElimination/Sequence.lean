import Counting.Algorithm.VariableElimination.Program
import Mathlib.Data.Fintype.Card

namespace Counting.Algorithm.VariableElimination

/-- A possibly partial supplied elimination sequence, indexed by its initial and
explicit remaining variable types. The type rules prevent eliminating twice. -/
inductive EliminationSequence : Type → Type → Type 1 where
  | nil (V : Type) : EliminationSequence V V
  | cons {V W : Type} (v : V) (rest : EliminationSequence (Remaining v) W) :
      EliminationSequence V W

namespace EliminationSequence

variable {V W D R : Type}

def length : {V W : Type} → EliminationSequence V W → Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ rest => rest.length + 1

/-- Execute a supplied prefix and return its factor list on the remaining variables. -/
def transform [Fintype D] [LinearOrder D] [CommSemiring R] :
    {V W : Type} → [Fintype V] → [LinearOrder V] →
      EliminationSequence V W → List (Factor V D R) → List (Factor W D R)
  | _, _, _, _, .nil _, fs => fs
  | _, _, _, _, .cons v rest, fs => rest.transform (eliminate v fs)

/-- The partition invariant holds after any prefix, with remaining variables explicit. -/
theorem partition_transform [Fintype D] [LinearOrder D] [CommSemiring R]
    {V W : Type} (sequence : EliminationSequence V W)
    [fv : Fintype V] [lv : LinearOrder V] [fw : Fintype W] [lw : LinearOrder W]
    (fs : List (Factor V D R)) :
    partition (sequence.transform fs) = partition fs := by
  revert fs
  revert fv lv fw lw
  induction sequence with
  | nil V =>
    intro fv lv fw lw fs
    have h : fv = fw := Subsingleton.elim _ _
    subst fw
    unfold partition
    congr
    exact Subsingleton.elim _ _
  | cons v rest ih =>
    intro fv lv fw lw fs
    exact (ih (eliminate v fs)).trans (partition_eliminate v fs)

/-- A prefix accounts for each eliminated variable and leaves exactly the others. -/
theorem length_add_card {V W : Type} (sequence : EliminationSequence V W)
    [fv : Fintype V] [dv : DecidableEq V] [fw : Fintype W] :
    sequence.length + Fintype.card W = Fintype.card V := by
  revert fv dv fw
  induction sequence with
  | nil V =>
    intro fv dv fw
    have h : fv = fw := Subsingleton.elim _ _
    subst fw
    simp [length]
  | @cons V W v rest ih =>
    intro fv dv fw
    have hc : Fintype.card (Remaining v) = Fintype.card V - 1 := by
      simp [Fintype.card_subtype_compl]
    have hp : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v⟩
    have hh := @ih (inferInstance : Fintype (Remaining v)) inferInstance fw
    simp only [length]
    rw [hc] at hh
    omega

end EliminationSequence
end Counting.Algorithm.VariableElimination
