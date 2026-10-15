import Counting.Algorithm.VariableElimination.Order

/-!
# Pinned occurrence semantics

Pinning a boundary assignment removes exactly the boundary ports of each input
occurrence. Hidden ports retain their original order and repetitions. The list
map retains duplicate occurrences, and the hidden-variable type retains isolated
variables. Neither construction requires an inhabited domain.
-/

namespace Counting.Algorithm.VariableElimination

variable {B V D R ι : Type} {L : Model.Language D R ι}

/-- Forget only the label, retaining the occurrence's ordered scope and table. -/
def occurrenceFactor (c : Model.Occurrence L V) : Factor V D R :=
  ⟨L.arity c.symbol, c.scope, L.value c.symbol⟩

@[simp] theorem eval_occurrenceFactor (c : Model.Occurrence L V) (a : V → D) :
    (occurrenceFactor c).eval a = c.eval a := rfl

/-- Original port positions that refer to hidden variables. -/
def hiddenPorts (c : Model.Occurrence L (B ⊕ V)) : Finset (Fin (L.arity c.symbol)) :=
  Finset.univ.filter fun i => (c.scope i).isRight

/-- Increasing enumeration of hidden ports; repeated variables are not identified. -/
def pinnedScope (c : Model.Occurrence L (B ⊕ V)) : Fin (hiddenPorts c).card → V :=
  fun j => (c.scope ((hiddenPorts c).orderIsoOfFin rfl j)).getRight (by
    have h := ((hiddenPorts c).orderIsoOfFin rfl j).property
    exact (Finset.mem_filter.mp h).2)

/-- Reinsert fixed boundary values into the full ordered input tuple. -/
def pinnedRow (c : Model.Occurrence L (B ⊕ V)) (a : B → D)
    (x : Fin (hiddenPorts c).card → D) : Fin (L.arity c.symbol) → D :=
  fun i => match h : c.scope i with
  | .inl b => a b
  | .inr _ => x (((hiddenPorts c).orderIsoOfFin rfl).symm ⟨i, by simp [hiddenPorts, h]⟩)

/-- A pinned occurrence is a factor on its actual hidden ports. This operation
creates a semantic value callback that `compileFactor` can materialize; it does
not enlarge the supplied signature language. -/
def pinOccurrence (a : B → D) (c : Model.Occurrence L (B ⊕ V)) : Factor V D R where
  arity := (hiddenPorts c).card
  scope := pinnedScope c
  value := fun x => L.value c.symbol (pinnedRow c a x)

@[simp] theorem pinnedRow_scope (c : Model.Occurrence L (B ⊕ V))
    (a : B → D) (b : V → D) :
    pinnedRow c a (b ∘ pinnedScope c) = Sum.elim a b ∘ c.scope := by
  funext i
  unfold pinnedRow
  split <;> rename_i h
  · simp [h]
  · simp [pinnedScope, h]

@[simp] theorem eval_pinOccurrence (a : B → D) (c : Model.Occurrence L (B ⊕ V))
    (b : V → D) :
    (pinOccurrence a c).eval b = c.eval (Sum.elim a b) := by
  simp [Factor.eval, pinOccurrence, Model.Occurrence.eval]

/-- Pin every occurrence independently, preserving list order and multiplicity. -/
def pinnedFactors (I : Model.OpenInstance L B V) (a : B → D) : List (Factor V D R) :=
  I.occurrences.map (pinOccurrence a)

@[simp] theorem length_pinnedFactors (I : Model.OpenInstance L B V) (a : B → D) :
    (pinnedFactors I a).length = I.occurrences.length := by simp [pinnedFactors]

@[simp] theorem weight_pinnedFactors [CommMonoid R]
    (I : Model.OpenInstance L B V) (a : B → D) (b : V → D) :
    weight (pinnedFactors I a) b = I.eval a b := by
  simp [weight, pinnedFactors, Model.OpenInstance.eval, List.map_map, Function.comp_def]

/-- The algorithm's partition function agrees with S1 for every boundary assignment,
including empty domains, nullary occurrences, and isolated hidden variables. -/
@[simp] theorem partition_pinnedFactors [CommSemiring R] [Fintype V] [DecidableEq V]
    [Fintype D] (I : Model.OpenInstance L B V) (a : B → D) :
    partition (pinnedFactors I a) = I.partition a := by
  simp [partition, Model.OpenInstance.partition]

/-- The actual supplied-order executor computes the S1 pinned partition table. -/
theorem evaluate_pinnedFactors [CommSemiring R] [Fintype V] [LinearOrder V]
    [Fintype D] [LinearOrder D] (order : EliminationOrder V)
    (I : Model.OpenInstance L B V) (a : B → D) :
    order.evaluate (pinnedFactors I a) = I.partition a := by
  rw [EliminationOrder.evaluate_eq_partition, partition_pinnedFactors]

/-- The canonical executable evaluator is correct at every S1 boundary assignment. -/
@[simp] theorem run_pinnedFactors [CommSemiring R] [Fintype V] [LinearOrder V]
    [Fintype D] [LinearOrder D] (I : Model.OpenInstance L B V) (a : B → D) :
    EliminationOrder.run (pinnedFactors I a) = I.partition a := by
  rw [EliminationOrder.run_eq_partition, partition_pinnedFactors]

end Counting.Algorithm.VariableElimination
