import Paper2.Paper1ProvedOddUnaryNRMatching

/-! The whole-family obstruction selects a genuine original graph outside
the sheared tensor criterion. Leastness quantifies over actual ordinary
same-table graphs, without adjoining mathematical factors as labels. -/
namespace Paper2.Paper1Proved.OddUnary.NR
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.RootIntegrationV1
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

private theorem closed_nullary {K : Type*} [Field K] (f : Holant.Signature K 0) : Closed f := by
  classical
  by_cases zero : f Fin.elim0=0
  · left
    funext x
    have x0 : x=Fin.elim0 := funext fun i => Fin.elim0 i
    change f x=0
    rw [x0]
    exact zero
  · let D : Holant.TensorDecomposition K 0 :=
      { count := 0
        arity := Fin.elim0
        factor := fun i => Fin.elim0 i
        ports := Equiv.equivOfIsEmpty _ _
        scale := Units.mk0 (f Fin.elim0) zero }
    refine Or.inr ⟨D,(fun i => Fin.elim0 i),?_⟩
    funext x
    have x0 : x=Fin.elim0 := funext fun i => Fin.elim0 i
    simp [Holant.TensorDecomposition.value,D,x0]

variable {r : ℕ} {b : ℕ → ℕ}
variable (K : IntermediateField ℚ AlgebraicComplex)
variable (H : (i : Fin r) → Holant.Signature K (b i.val))
variable (A : Holant.Tractable.InvertibleKernel)

/-- Some original row must fail the single common NR chart. The conclusion
comes from the whole-language tractability obstruction itself. -/
theorem outside_coordinate_row
    (iso : A.matrix false false^2+A.matrix true false^2=0)
    (negative : ¬Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H)) :
    ∃ i : Fin r,¬Closed (A.symm.action (RingHomRealization.mapSignature K.subtype (H i))) := by
  classical
  by_contra none
  apply negative
  apply tract_of_closed_coordinates A iso
    (GlobalCloseCompletionUnaryDescentSource.ambient K H)
    (Set.finite_range (fun i : Fin r =>
      (⟨b i.val,GlobalCloseCompletionUnaryDescentSource.mapped K H i⟩ : AnySignature AlgebraicComplex)))
  rintro f ⟨i,rfl⟩
  by_contra outside
  exact none ⟨i,outside⟩

/-- The selected mathematical row is the denotation of its retained corolla
with only original labels and ordinary edges. -/
theorem outside_coordinate_graph
    (iso : A.matrix false false^2+A.matrix true false^2=0)
    (negative : ¬Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H)) :
    ∃ n,∃ N : NoXOrdinaryGraphAdjoin.Output H n,
      ¬Closed (A.symm.action (RingHomRealization.mapSignature K.subtype N.network.denote)) := by
  obtain ⟨i,outside⟩ := outside_coordinate_row K H A iso negative
  refine ⟨b i.val,GlobalCloseCompletionUnaryWholeFamilySelector.row K H i,?_⟩
  rwa [GlobalCloseCompletionUnaryWholeFamilySelector.row_value]

private theorem outside_positive {n : ℕ} (N : NoXOrdinaryGraphAdjoin.Output H n)
    (outside : ¬Closed (A.symm.action (RingHomRealization.mapSignature K.subtype N.network.denote))) :
    0<n := by
  cases n with
  | zero => exact False.elim (outside (closed_nullary _))
  | succ n => exact Nat.zero_lt_succ n

/-- A minimum is an actual graph over the unchanged field and row table.
Unlike a prime-factor minimum, it also retains genuine unary exits. -/
structure CoordinateMinimum where
  arity : ℕ
  positive : 0<arity
  graph : NoXOrdinaryGraphAdjoin.Output H arity
  outside : ¬Closed (A.symm.action (RingHomRealization.mapSignature K.subtype graph.network.denote))
  least : ∀ m,∀ N : NoXOrdinaryGraphAdjoin.Output H m,
    ¬Closed (A.symm.action (RingHomRealization.mapSignature K.subtype N.network.denote)) → arity≤m

theorem coordinate_minimum_exists
    (available : ∃ n,∃ N : NoXOrdinaryGraphAdjoin.Output H n,
      ¬Closed (A.symm.action (RingHomRealization.mapSignature K.subtype N.network.denote))) :
    Nonempty (CoordinateMinimum K H A) := by
  classical
  let P : ℕ → Prop := fun n => ∃ N : NoXOrdinaryGraphAdjoin.Output H n,
    ¬Closed (A.symm.action (RingHomRealization.mapSignature K.subtype N.network.denote))
  have hav : ∃ n,P n := available
  obtain ⟨N,outside⟩ := Nat.find_spec hav
  exact ⟨{
    arity := Nat.find hav
    positive := outside_positive K H A N outside
    graph := N
    outside := outside
    least := fun m V hv => Nat.find_min' hav ⟨V,hv⟩ }⟩

/-- No outside-class source assumption is supplied: failure of the original
whole-family criterion constructs the actual minimum. -/
theorem whole_family_coordinate_minimum
    (iso : A.matrix false false^2+A.matrix true false^2=0)
    (negative : ¬Tract (GlobalCloseCompletionUnaryDescentSource.ambient K H)) :
    Nonempty (CoordinateMinimum K H A) :=
  coordinate_minimum_exists K H A (outside_coordinate_graph K H A iso negative)

namespace CoordinateMinimum
variable {K H A} (M : CoordinateMinimum K H A)

/-- Every genuinely smaller actual graph lies in the NR chart. -/
theorem smaller_closed {m : ℕ} (bound : m<M.arity)
    (N : NoXOrdinaryGraphAdjoin.Output H m) :
    Closed (A.symm.action (RingHomRealization.mapSignature K.subtype N.network.denote)) := by
  classical
  by_contra outside
  have lower := M.least m N outside
  omega
end CoordinateMinimum

end
end Paper2.Paper1Proved.OddUnary.NR

