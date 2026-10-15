import Paper2.ExactInput.Recognition.NativeCertifiedCatalogue
import Paper2.ExactInput.Recognition.NativeKSystemLayout
import Holant.Proofs.Recognition.RuntimeSupportTable

/-! A complete certificate catalogue contains a literal descriptor tuple for
every forward-K coefficient. These are algebraic completeness witnesses;
none of the selected coefficients or heights is an input to the converter. -/
namespace Paper2.ExactInput.Recognition.NativeExpectedTable
open Holant Holant.Tractable
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.RemoteWork.TractChainV1
open NativeKSystemLayout
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev count (d : RuntimeSupportTable.Data) := (coefficientCatalogue d.arity).length

def value (d : RuntimeSupportTable.Data)
    (p : LocalAffineVariableLayout.Parameters d.arity) : AlgebraicComplex :=
  match p with
  | ⟨.inl i,x⟩ => sourceKBasis.action (d.G i) x
  | ⟨.inr _,_⟩ => 0

def values (d : RuntimeSupportTable.Data) : Fin (count d) → AlgebraicComplex :=
  fun j => value d ((coefficientCatalogue d.arity).get j)

def index (d : RuntimeSupportTable.Data) (i : Fin d.count)
    (x : Fin (d.arity i) → Bool) : Fin (count d) :=
  ⟨(LocalAffineVariableLayout.address d.arity ⟨.inl i,x⟩).val,
    coefficientAddress_lt d.arity i x⟩

@[simp] theorem values_at (d : RuntimeSupportTable.Data) (i : Fin d.count)
    (x : Fin (d.arity i) → Bool) :
    values d (index d i x)=sourceKBasis.action (d.G i) x := by
  have hi : index d i x =
      ⟨(coefficientCatalogue d.arity).idxOf ⟨.inl i,x⟩,
        List.idxOf_lt_length_of_mem (mem_coefficientCatalogue d.arity i x)⟩ :=
    Fin.ext (coefficient_address_eq d.arity i x)
  unfold values
  rw [hi]
  have h : (coefficientCatalogue d.arity).get
      ⟨(coefficientCatalogue d.arity).idxOf ⟨.inl i,x⟩,
        List.idxOf_lt_length_of_mem (mem_coefficientCatalogue d.arity i x)⟩ = ⟨.inl i,x⟩ := by
    exact List.getElem_idxOf (List.idxOf_lt_length_of_mem (mem_coefficientCatalogue d.arity i x))
  rw [h]
  rfl

/-- Completeness includes zero values, scalar tables, and empty families. -/
theorem exists_tuple (d : RuntimeSupportTable.Data) :
    ∃ cs : List RootCode, ∃ H : ℕ,
      (∀ height ≥ H, cs ∈ NativeCertifiedCatalogue.tuples (count d) height) ∧
      ∀ i x, (cs.getD (index d i x).val (RationalRootCode.code 0)).Represents
        (sourceKBasis.action (d.G i) x : ℂ) := by
  obtain ⟨c,H,hc,hH⟩ := NativeCertifiedCatalogue.tuples_covers_fn (values d)
  refine ⟨List.ofFn c,H,hH,?_⟩
  intro i x
  rw [PositiveCertificateMachine.getD_ofFn]
  simpa only [values_at] using hc (index d i x)

end
end Paper2.ExactInput.Recognition.NativeExpectedTable
