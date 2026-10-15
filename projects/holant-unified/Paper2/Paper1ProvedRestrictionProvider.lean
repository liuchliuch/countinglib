import Paper2.Paper1ProvedEOProvider
import Holant.Proofs.Reductions.CanonicalFamily.Semantics

/-! Literal subfamily restriction executes the proved finite label lookup and
row scanner. Every ordered incidence and edge remains in its original place;
the complete canonical field-output oracle controller carries query bounds. -/
namespace Paper2.Paper1Proved
open Paper2.Tractable Paper2.ExactInput Paper2.Problem
open Paper2.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.Hardness
open Holant.Complexity.UniversalPairReduction.Surgery
noncomputable section
set_option backward.isDefEq.respectTransparency false

def restrictionLabel (L M : Language) (h : L.family ⊆ M.family) :
    Fin L.count → Fin M.count :=
  fun i => Classical.choose (h ⟨i,rfl⟩)

theorem restrictionLabel_literal (L M : Language) (h : L.family ⊆ M.family)
    (i : Fin L.count) :
    (⟨M.arity (restrictionLabel L M h i).val,M.signature (restrictionLabel L M h i)⟩ :
      AnySignature AlgebraicComplex) = ⟨L.arity i.val,L.signature i⟩ :=
  Classical.choose_spec (h ⟨i,rfl⟩)

theorem restrictionLabel_arity (L M : Language) (h : L.family ⊆ M.family)
    (i : Fin L.count) : M.arity (restrictionLabel L M h i).val = L.arity i.val :=
  congrArg Sigma.fst (restrictionLabel_literal L M h i)

def restrictionInput (L M : Language) (h : L.family ⊆ M.family) :
    Instance L → Instance M :=
  fun G => (inputIso M).symm (CanonicalFamily.Relabel.input (restrictionLabel L M h)
    (restrictionLabel_arity L M h) (input L G))

def restrictionComputes (L M : Language) (h : L.family ⊆ M.family) :
    Computes (inputEncoding L) (inputEncoding M) (restrictionInput L M h) :=
  recode (TractableAlgorithms.Paper1Machine.computes
    (CanonicalFamily.Relabel.computes (restrictionLabel L M h)
      (restrictionLabel_arity L M h))) (input L) (input_bytes L)
    (fun G => input_bytes_back M _)

theorem restrictionValue (L M : Language) (h : L.family ⊆ M.family)
    (G : Instance L) :
    Problem.value .nativeX L G = Problem.value .nativeX M (restrictionInput L M h G) := by
  let σ := restrictionLabel L M h
  let ha := restrictionLabel_arity L M h
  let r := input L G
  have rows : ∀ i : Fin L.count, ∀ bits,
      Choice.table (signatures L) i.val bits =
        (1 : AlgebraicComplex) * Choice.table (signatures M) (σ i).val bits := by
    intro i bits
    have hl := restrictionLabel_literal L M h i
    have he := congrArg (fun f : AnySignature AlgebraicComplex =>
      f.2 (fun j => bits.getD j.val false)) hl
    simpa [Choice.table,σ,i.isLt,(σ i).isLt] using he.symm
  have ones : RootPreprocessing.OccurrenceProduct.value
      (fun _ : Fin L.count => (1 : AlgebraicComplex)) r.val = 1 := by
    unfold RootPreprocessing.OccurrenceProduct.value
    have hm : r.val.vertices.map (fun row => RootPreprocessing.OccurrenceProduct.total
        (fun _ : Fin L.count => (1 : AlgebraicComplex)) row.1) =
        r.val.vertices.map (fun _ => (1 : AlgebraicComplex)) := by
      apply List.map_congr_left
      intro row hr
      have hi := ((Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.RawGrouping.wellFormed_iff_members
        _ _ _ _).mp r.property).1 row hr
      simp [RootPreprocessing.OccurrenceProduct.total,hi.1]
    rw [hm]
    simp
  have hv := CanonicalFamily.Relabel.value_scaled σ (Choice.table (signatures L))
    (Choice.table (signatures M)) (fun _ => (1 : AlgebraicComplex)) ha r rows
  rw [ones,one_mul] at hv
  have hs := network_value .nativeX L G
  have ht := network_value .nativeX M (restrictionInput L M h G)
  rw [show Paper2.Paper1Proved.kernels .nativeX =
    (fun _ : Fin 1 => Holant.Signature.disequality) from rfl] at hs ht
  rw [Choice.denote_eq_evaluate] at hs ht
  have hi : input M (restrictionInput L M h G) = CanonicalFamily.Relabel.input σ ha r :=
    (inputIso M).apply_symm_apply _
  change Choice.evaluate (Choice.table (signatures M))
    (input M (restrictionInput L M h G)).val.edges.length
    (input M (restrictionInput L M h G)).val.vertices = _ at ht
  rw [hi] at ht
  exact hs.symm.trans (hv.trans ht)

theorem restriction (L M : Language) (h : L.family ⊆ M.family) :
    FixedFieldOutput.Reduces .nativeX L M :=
  ⟨FixedFieldOutput.sameValueReduction .nativeX .nativeX L M
    (restrictionInput L M h) (restrictionComputes L M h) (restrictionValue L M h)⟩

theorem restrictionProvider : SourceFaithful.Paper1RestrictionAccepted :=
  ⟨restriction⟩

end
end Paper2.Paper1Proved
