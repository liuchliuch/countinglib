import Paper2.DegreeCSP.EqualityDegreeTemplates
import Paper2.DegreeCSP.EqualityTemplateRows

/-! The degree divisibility cast preserves every serialized endpoint and row.
The output is exactly the literal macro list consumed by the runtime compiler. -/
namespace Paper2.DegreeCSP.EqualityDegreeTemplates
open Paper2.Tractable Paper2.ExactInput
open Holant.Complexity Holant.Complexity.RawClosedNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

def degreeRow (k : ℕ) (hk : 3 ≤ k) (d : ℕ) (hd : k ∣ d) (label outer inner : ℕ)
    (v : Fin (make k hk d hd).shape.vertices) : RawVertex :=
  (label,List.ofFn (fun j : Fin k => EqualityTemplates.serializedEndpoint outer inner
    ((make k hk d hd).shape.ports ⟨v,Fin.cast (make_arity k hk d hd v).symm j⟩)))

def networkRows {n : ℕ} (N : Network AlgebraicComplex n) (label outer inner : ℕ) : List RawVertex :=
  List.ofFn (fun v : Fin N.shape.vertices => (label,List.ofFn (fun j : Fin (N.shape.arity v) =>
    EqualityTemplates.serializedEndpoint outer inner (N.shape.ports ⟨v,j⟩))))

theorem degree_rows_eq_networkRows (k : ℕ) (hk : 3 ≤ k) (d : ℕ) (hd : k ∣ d)
    (label outer inner : ℕ) : List.ofFn (degreeRow k hk d hd label outer inner) =
      networkRows (make k hk d hd) label outer inner := by
  unfold degreeRow networkRows
  apply congrArg List.ofFn
  funext v
  congr 1
  exact (List.ofFn_congr (make_arity k hk d hd v)
    (fun j => EqualityTemplates.serializedEndpoint outer inner ((make k hk d hd).shape.ports ⟨v,j⟩))).symm

theorem networkRows_reindex {n d : ℕ} (N : Network AlgebraicComplex n) (h : n=d)
    (label outer inner : ℕ) :
    networkRows (N.reindexBoundary (finCongr h)) label outer inner=networkRows N label outer inner := by
  unfold networkRows
  apply congrArg List.ofFn
  funext v
  congr 1
  apply congrArg List.ofFn
  funext j
  change EqualityTemplates.serializedEndpoint outer inner
    ((Equiv.sumCongr (finCongr h) (Equiv.refl _)) (N.shape.ports ⟨v,j⟩)) = _
  cases N.shape.ports ⟨v,j⟩ <;> rfl

/-- Every raw row is obtained in the same order, including a degree-zero
variable's two literal equality rows. -/
theorem degree_rows (k : ℕ) (hk : 3 ≤ k) (d : ℕ) (hd : k ∣ d) (label outer inner : ℕ) :
    List.ofFn (degreeRow k hk d hd label outer inner) =
      ComputationLayout.macroRows k label d outer inner := by
  rw [degree_rows_eq_networkRows]
  by_cases h0 : d=0
  · subst d
    rw [make_zero]
    exact EqualityTemplates.nullary_rows k label outer inner
  · rw [make_positive k hk d hd h0,networkRows_reindex]
    change List.ofFn (EqualityTemplates.positiveRow (d/k) k hk label outer inner) = _
    rw [EqualityTemplates.positive_rows]
    simp only [ComputationLayout.macroRows,if_neg h0,ComputationLayout.multiplicity]

end
end Paper2.DegreeCSP.EqualityDegreeTemplates
