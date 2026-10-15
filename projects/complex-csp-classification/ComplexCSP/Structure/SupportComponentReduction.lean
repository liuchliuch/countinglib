import ComplexCSP.Structure.SupportComponentSemantics
import ComplexCSP.Instances.MatrixCSPComponents
import ComplexCSP.Instances.RootedCSPFunctionalRecovery

/-! # Charged support-closed color restriction for unrestricted graph CSP

First compute every connected input component. On each component recover one
root-subset functional with a fixed finite family of real gadget queries. The
algorithm does not simultaneously pin an unbounded number of vertices.
-/
noncomputable section
open Classical
namespace ComplexCSP.SupportComponentReduction
open PlanarHom PlanarHom.Complexity PairProjectionMachines
open ComplexityCSPCode MatrixCSPCodeMixed RootedCSPProjection
open RootedCSPFunctionalRecovery SupportComponentSemantics
variable {D K : Type} [Fintype D] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable [Algebra ℚ K] {dimension : ℕ}

/-- The connected-input part of the reduction uses actual fresh-root attachments. -/
def connectedReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (A : D → D → K) (hs : ∀ i j,A i j=A j i)
    (X : Set D) (hX : RootedRestriction.ColorClosed A X) :
    PromisePolyTimeTuringReduction
      (MatrixCSPComponents.connectedProblem (fun i j : X => A i.val j.val) basis)
      (ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis) := by
  let P := chooseFunctional (MatrixCSP.language A) (subsetWeight X)
  let prepare : Code → Bits × List Code := fun g => ([],queries P g)
  have hp : FP encoding (BitEncoding.bits.prod encoding.list) prepare :=
    (fp_const encoding BitEncoding.bits []).pair (fp_queries P)
  let recover : Bits × List K → K := fun p => RootedCSPRecovery.recover P.coefficients p.2
  have hr : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover :=
    (fp_snd _ _).comp (RootedCSPRecovery.fp_recover basis P.coefficients)
  let target := MatrixCSPComponents.connectedProblem (fun i j : X => A i.val j.val) basis
  let source := ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis
  let view : ∀ raw,target.valid raw → Code := fun _ h => h.choose
  have hview : ∀ raw h,encoding.encode (view raw h)=raw := fun _ h => h.choose_spec.2
  let p := Classical.choose (exists_partition_output_bound (MatrixCSP.language A) basis)
  have hbound := Classical.choose_spec (exists_partition_output_bound (MatrixCSP.language A) basis)
  refine nonadaptiveReduction encoding BitEncoding.bits encoding (numberFieldEncoding basis)
    (numberFieldEncoding basis) target source prepare (partition (MatrixCSP.language A)) recover
    (Classical.choice hp) (Classical.choice hr) view hview ?_ ?_ ?_ p ?_
  · intro raw h q hq
    exact ⟨_,queries_valid P _ h.choose_spec.1.1 h.choose_spec.1.2.2 q hq,rfl⟩
  · intro q _
    exact encodedFunction_encode encoding (numberFieldEncoding basis) (partition (MatrixCSP.language A)) [] q
  · intro raw h
    have hg := h.choose_spec.1
    have hsem := connected_submatrix A hs X hX (toMixed (view raw h))
      (valid A _ hg.1) hg.2.1 hg.2.2
    rw [toCode_toMixed A _ hg.1] at hsem
    change (numberFieldEncoding basis).encode
      (RootedCSPRecovery.recover P.coefficients
        ((queries P (view raw h)).map (partition (MatrixCSP.language A)))) =
      encodedFunction encoding (numberFieldEncoding basis)
        (partition (MatrixCSP.language (fun i j : X => A i.val j.val))) [] raw
    conv_rhs => rw [←hview raw h,encodedFunction_encode]
    rw [recover_queries P _ hg.1 hg.2.2]
    exact congrArg (numberFieldEncoding basis).encode hsem
  · intro raw h
    obtain ⟨g,hg,rfl⟩ := h
    simpa only [source,ComplexityCSPCountReduction.partitionProblem,encodedFunction_encode] using hbound g

/-- Complete general-graph support-closed restriction, with computed component
queries, exact product recovery, and the empty graph and all isolates included. -/
def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (A : D → D → K) (hs : ∀ i j,A i j=A j i)
    (X : Set D) (hX : RootedRestriction.ColorClosed A X) :
    PromisePolyTimeTuringReduction
      (ComplexityCSPCountReduction.partitionProblem
        (MatrixCSP.language (fun i j : X => A i.val j.val)) basis)
      (ComplexityCSPCountReduction.partitionProblem (MatrixCSP.language A) basis) :=
  (MatrixCSPComponents.reduction (fun i j : X => A i.val j.val) basis).trans
    (connectedReduction basis A hs X hX)

end ComplexCSP.SupportComponentReduction
