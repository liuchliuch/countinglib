import ComplexCSP.Structure.MaltsevTypeAlgebra
import ComplexCSP.Structure.MaltsevWitnessInsert

/-! # Closed support restrictions preserve the actual row Type Partition

This supplies a coordinate-pinning alternative to permuting a marginal's row
callback. It derives the required Type Partition from the existing common
row-equivalence operation, rather than assuming a restricted type oracle.
-/
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {d n : ℕ} {A : Type*}

/-- Any preserved subrelation retains preservation of the literal same-label
row-equivalence relation. -/
theorem row_equivalence_restrict {m : Operation (Fin d)}
    {R S : Set (Fin n → Fin d)} (hSR : S ⊆ R) (hS : Preserves m S)
    {label : Tuple (Fin d) n → A}
    (hEq : PreservesRowEquivalence m (labelFiber R label)) :
    PreservesRowEquivalence m (labelFiber S label) := by
  intro x x' y y' z z'
  rintro ⟨a,⟨hx,hxa⟩,⟨hx',hx'a⟩⟩ ⟨b,⟨hy,hyb⟩,⟨hy',hy'b⟩⟩ ⟨c,⟨hz,hzc⟩,⟨hz',hz'c⟩⟩
  obtain ⟨q,hq,hq'⟩ := hEq x x' y y' z z'
    ⟨a,⟨hSR hx,hxa⟩,⟨hSR hx',hx'a⟩⟩
    ⟨b,⟨hSR hy,hyb⟩,⟨hSR hy',hy'b⟩⟩
    ⟨c,⟨hSR hz,hzc⟩,⟨hSR hz',hz'c⟩⟩
  exact ⟨q,⟨hS x hx y hy z hz,hq.2⟩,⟨hS x' hx' y' hy' z' hz',hq'.2⟩⟩

/-- The Type Partition is derived for every coordinate order after restriction. -/
theorem allTypesPartition_restrict {m : Operation (Fin d)} (hm : IsMaltsev m)
    {R S : Set (Fin n → Fin d)} (hSR : S ⊆ R) (hS : Preserves m S)
    {label : Tuple (Fin d) n → A}
    (hEq : PreservesRowEquivalence m (labelFiber R label)) : AllTypesPartition S label :=
  allTypesPartition_of_row_equivalence hm (row_equivalence_restrict hSR hS hEq)

def coordinatePin (R : Set (Fin n → Fin d)) (i : Fin n) (a : Fin d) : Set (Fin n → Fin d) :=
  {x | x ∈ R ∧ x i = a}

theorem coordinatePin_preserves {m : Operation (Fin d)} (hm : IsMaltsev m)
    {R : Set (Fin n → Fin d)} (hR : Preserves m R) (i : Fin n) (a : Fin d) :
    Preserves m (coordinatePin R i a) := by
  intro x hx y hy z hz
  refine ⟨hR x hx.1 y hy.1 z hz.1,?_⟩
  simp only [map₃,hx.2,hy.2,hz.2]
  exact hm.1 a a

def coordinatePinCode (m : Operation (Fin d)) (W : Code (Fin d) n)
    (i : Fin n) (a : Fin d) : StoredCode d n :=
  storeCode (insertConstraint m W (fun _ : Fin 1 => i) (fun x => decide (x 0 = a)))

/-- The pin witness is the actual fixed-unary-constraint insertion algorithm;
its bounded projections have arity at most two. -/
theorem coordinatePinCode_correct {m : Operation (Fin d)} (hm : IsMaltsev m)
    {W : Code (Fin d) n} {R : Set (Fin n → Fin d)} (hR : Preserves m R) (hW : Correct W R)
    (i : Fin n) (a : Fin d) : Correct (coordinatePinCode m W i a).toCode (coordinatePin R i a) := by
  have hc : Preserves m {x : Fin 1 → Fin d | decide (x 0 = a) = true} := by
    intro x hx y hy z hz
    simp only [Set.mem_ofPred_eq,decide_eq_true_eq] at hx hy hz ⊢
    simp only [map₃,hx,hy,hz]
    exact hm.1 a a
  have h := insertConstraint_correct hm hR hW (fun _ : Fin 1 => i) (fun x => decide (x 0 = a)) hc
  simpa only [coordinatePinCode,storeCode_toCode,constraintRelation,coordinatePin,
    decide_eq_true_eq,Function.comp_apply] using h

theorem coordinatePin_typesPartition {m : Operation (Fin d)} (hm : IsMaltsev m)
    {R : Set (Fin n → Fin d)} {label : Tuple (Fin d) n → A}
    (hEq : PreservesRowEquivalence m (labelFiber R label)) (i : Fin n) (a : Fin d) :
    TypesPartition (coordinatePin R i a) label := by
  exact (allTypesPartition_restrict hm (fun _ hx => hx.1)
    (coordinatePin_preserves hm (row_equivalence_support_preserves hEq) i a) hEq).base

end ComplexCSP.MaltsevWitness
