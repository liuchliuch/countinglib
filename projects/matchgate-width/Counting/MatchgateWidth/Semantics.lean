import Counting.Model.Basic
import MatchgateWidth.OrderedAllLeftGadget
import MatchgateWidth.LabelledInstanceClasses

/-!
# Exact occurrence semantics for labelled matchgate-width instances

The adapter retains the left/right label as a disjoint-sum tag, one occurrence
per original vertex, every port in its original order, and the original finite
edge set. It carries no complexity claim or new planar-normalization theorem.
Open gadgets retain their `Fin n` boundary pointwise; geometry remains available
on the original instance and is never inferred from a partition identity.
-/
namespace Counting.MatchgateWidth.Semantics
noncomputable section
open scoped BigOperators
open _root_.MatchgateWidth

variable {S T : LabelledShape} {D E : Type} {a b c n : ℕ}

/-- Keep both finite label sets and their arities, including zero arities. -/
def language (F : LabelledLanguage S D) : Model.Language D ℂ (S.LeftLabel ⊕ S.RightLabel) where
  arity := Sum.elim S.leftArity S.rightArity
  value := fun l => match l with
    | .inl l => F.left l
    | .inr l => F.right l

/-- One occurrence for each original left and right vertex; hidden variables
are exactly the original edges. Coincident tables retain distinct labels. -/
def closedInstance (I : LabelledInstance S a b c) (F : LabelledLanguage S D) :
    Model.OpenInstance (language F) Empty (Fin c) where
  occurrences :=
    List.ofFn (fun v : Fin a =>
      ⟨Sum.inl (I.leftLabel v), fun i => Sum.inr (I.leftIncidence ⟨v, i⟩)⟩) ++
    List.ofFn (fun v : Fin b =>
      ⟨Sum.inr (I.rightLabel v), fun i => Sum.inr (I.rightIncidence ⟨v, i⟩)⟩)

/-- Nullary vertices are counted as occurrences even though they use no edge. -/
@[simp] theorem closedInstance_occurrences_length
    (I : LabelledInstance S a b c) (F : LabelledLanguage S D) :
    (closedInstance I F).occurrences.length = a + b := by
  simp [closedInstance]

/-- Equality of assignment products before summation. -/
theorem closedInstance_eval (I : LabelledInstance S a b c) (F : LabelledLanguage S D)
    (z : Empty → D) (x : Fin c → D) :
    (closedInstance I F).eval z x =
      (∏ v, F.left (I.leftLabel v) (fun i => x (I.leftIncidence ⟨v, i⟩))) *
      ∏ v, F.right (I.rightLabel v) (fun i => x (I.rightIncidence ⟨v, i⟩)) := by
  unfold Model.OpenInstance.eval closedInstance
  rw [List.map_append, List.prod_append]
  simp only [List.map_ofFn, List.prod_ofFn]
  rfl

/-- The unified closed partition equals the original labelled instance value
for every finite domain, without planarity, rank, or nonempty-domain premises. -/
@[simp] theorem closedInstance_partition [Fintype D]
    (I : LabelledInstance S a b c) (F : LabelledLanguage S D) (z : Empty → D) :
    (closedInstance I F).partition z = I.value F := by
  classical
  simp only [Model.OpenInstance.partition, closedInstance_eval, LabelledInstance.value]

/-- Open occurrence semantics with the original ordered boundary and internal
edge variables. Swapping the sum tags only puts boundary before hidden variables. -/
def openInstance (I : AllLeftGadget S a b c n) (F : LabelledLanguage S D) :
    Model.OpenInstance (language F) (Fin n) (Fin c) where
  occurrences :=
    List.ofFn (fun v : Fin a =>
      ⟨Sum.inl (I.leftLabel v), fun i => (I.leftIncidence ⟨v, i⟩).swap⟩) ++
    List.ofFn (fun v : Fin b =>
      ⟨Sum.inr (I.rightLabel v), fun i => Sum.inr (I.rightIncidence ⟨v, i⟩)⟩)

@[simp] theorem openInstance_occurrences_length
    (I : AllLeftGadget S a b c n) (F : LabelledLanguage S D) :
    (openInstance I F).occurrences.length = a + b := by
  simp [openInstance]

private theorem elim_swap (x : Fin c → D) (z : Fin n → D) (e : Fin c ⊕ Fin n) :
    Sum.elim z x e.swap = Sum.elim x z e := by
  cases e <;> rfl

/-- The original open tensor is the unified partition table at every ordered
boundary assignment, including an empty boundary and scalar nullary factors. -/
@[simp] theorem openInstance_partition [Fintype D]
    (I : AllLeftGadget S a b c n) (F : LabelledLanguage S D) (z : Fin n → D) :
    (openInstance I F).partition z = I.value F z := by
  classical
  rw [AllLeftGadget.value_eq]
  unfold Model.OpenInstance.partition
  apply Finset.sum_congr (by ext; simp)
  intro x _
  unfold Model.OpenInstance.eval openInstance
  rw [List.map_append, List.prod_append]
  simp only [List.map_ofFn, List.prod_ofFn]
  simp only [Model.Occurrence.eval, language, Function.comp_def, Sum.elim_inr, elim_swap]
  congr 1

/-- Transport the substantive boundary-support theorem to the public partition
model, preserving the actual unique primitive endpoint and its exact port. -/
theorem partition_boundary_support_le [Fintype D]
    (I : AllLeftGadget S a b c n) (F : LabelledLanguage S D) (p : Fin n) :
    columnSupport (portFlatten ((openInstance I F).partition) p) ≤
      columnSupport (portFlatten (F.left (I.leftLabel (I.boundaryVertex p)))
        (I.boundaryPort p)) := by
  have h : (openInstance I F).partition = I.value F := by
    funext z
    exact openInstance_partition I F z
  rw [h]
  simpa only [columnSupport, Matrix.range_mulVecLin] using I.boundary_support_le F p

/-- Exact labelled equivalence is also equivalence of the unified partitions
on the same incidence structure and the same allowed class of instances. -/
theorem exactlyLabelledEquivalentOn_iff_partition [Fintype D] [Fintype E]
    (C : LabelledInstanceClass S) (F : LabelledLanguage S D) (G : LabelledLanguage T E) :
    ExactlyLabelledEquivalentOn C F G ↔
      ∃ e : LabelledShapeEquiv S T, ∀ a b c (I : LabelledInstance S a b c),
        C a b c I →
        (closedInstance I F).partition Empty.elim =
          (closedInstance I (e.pullback G)).partition Empty.elim := by
  simp only [closedInstance_partition, ExactlyLabelledEquivalentOn]

end
end Counting.MatchgateWidth.Semantics
