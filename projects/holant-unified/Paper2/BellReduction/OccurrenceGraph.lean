import Paper2.BellReduction.NetworkTensor
import Paper2.Certificates.BellClosures
import Paper2.ReedMuller

/-! Source Lemma 8.12's occurrence identity as an actual two-vertex native-X
network. The original scalar and the ordered Y sign are recorded explicitly. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.BellReduction
open Bell Bell.Closures ReedMuller
variable {K : Type} [CommRing K]

/-- First close old-core port 0 to binary port 0; then close core port 1 to
binary port 1. The six remaining core ports preserve their original order. -/
def occurrenceOrder : Equiv.Perm (Fin 10) where
  toFun := ![0,2,4,5,6,7,8,9,1,3]
  invFun := ![0,8,1,9,2,3,4,5,6,7]
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def bellTable (d l : Bool) : Signature K 2 := fun x => ordered d l (x 0) (x 1)

/-- Exactly one complete RM8 input vertex and one ordered Bell vertex, joined
by two genuine native-X edges. No Bell-labelled structural wire is used. -/
noncomputable def occurrenceGraph (c : K) (d l : Bool) : Network K 6 :=
  ((((Network.corolla (fun x => c * core x)).tensor
    (Network.corolla (bellTable d l))).reindexBoundary occurrenceOrder).contract
      Signature.disequality).contract Signature.disequality

/-- The two contractions retain the bilinear native-X effective kernel XbX. -/
theorem occurrenceGraph_denote (c : K) (d l : Bool) :
    (occurrenceGraph c d l).denote = fun x =>
      c * sign l * bellTriple d l x := by
  funext x
  rw [occurrenceGraph,Network.denote_contract,Network.denote_contract,
    Network.denote_reindexBoundary,Network.denote_tensor,
    Network.denote_corolla,Network.denote_corolla]
  simp only [Signature.contract_disequality,Tensor.reindex_apply,
    Signature.tensor_apply,bellTable]
  have hm (a u b v : Bool) :
      (core (K := K) (fun i : Fin 8 =>
        (Fin.cons a (Fin.cons u (Fin.cons b (Fin.cons v x))) : Fin 10 → Bool)
          (occurrenceOrder (Fin.castAdd 2 i)))) = core (Fin.cons a (Fin.cons b x)) := by
    apply congrArg (core (K := K))
    funext i
    fin_cases i <;> rfl
  simp only [hm]
  change
    c * core (Fin.cons false (Fin.cons false x)) * ordered d l true true +
    c * core (Fin.cons true (Fin.cons false x)) * ordered d l false true +
    (c * core (Fin.cons false (Fin.cons true x)) * ordered d l true false +
    c * core (Fin.cons true (Fin.cons true x)) * ordered d l false false) = _
  have h := congrFun (contract_core_bell (K := K) d l) x
  simp only [Signature.contract,Fintype.sum_bool] at h
  rw [← h]
  cases d <;> cases l <;> simp [ordered,sign] <;> ring

/-- The complete RM8 scalar and Bell sign are never dropped. -/
theorem occurrenceGraph_scalar_ne_zero [Nontrivial K] [NoZeroDivisors K]
    {c : K} (hc : c ≠ 0) (l : Bool) : c * sign l ≠ 0 := by
  apply mul_ne_zero hc
  cases l <;> simp [sign]

theorem occurrenceGraph_sizes (c : K) (d l : Bool) :
    (occurrenceGraph c d l).shape.vertices = 2 ∧
      (occurrenceGraph c d l).shape.edges = 2 := by
  simp [occurrenceGraph,Network.reindexBoundary,Network.contract,
    Network.corolla,Network.tensor,FiniteNetwork.toNetwork]

/-- Both genuine input resources are retained with their exact literal labels. -/
theorem occurrenceGraph_uses (c : K) (d l : Bool) {F : SignatureFamily K}
    (hcore : (⟨8,fun x => c * core x⟩ : AnySignature K) ∈ F)
    (hbell : (⟨2,bellTable d l⟩ : AnySignature K) ∈ F) :
    (occurrenceGraph c d l).Uses F := by
  have h₁ : (Network.corolla (fun x => c * core x)).Uses F := fun _ => hcore
  have h₂ : (Network.corolla (bellTable d l)).Uses F := fun _ => hbell
  exact (((Network.Uses.tensor h₁ h₂).reindexBoundary occurrenceOrder).contract _).contract _

theorem occurrenceGraph_native (c : K) (d l : Bool) :
    (occurrenceGraph c d l).NativeX := by
  apply Network.NativeX.contract
  apply Network.NativeX.contract
  apply Network.NativeX.reindexBoundary
  apply Network.NativeX.tensor
  · intro e
    exact Fin.elim0 e
  · intro e
    exact Fin.elim0 e

end Paper2.BellReduction
