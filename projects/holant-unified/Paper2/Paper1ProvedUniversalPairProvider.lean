import Paper2.Paper1ProvedOracleAdapters
import Paper2.SourceFaithful.OccurrenceInputs
import Holant.Proofs.Hardness.GeneralEOSinglePinSource

/-! Actual source Lemma 3.2 for the literal distinguished-label convention of
Paper 2. The genuine source programme counts at most one NEW carrier label.
An explicit finite relabelling moves that label from first to last; coincident
old tensors are preserved and are never counted as carrier occurrences. -/
namespace Paper2.Paper1Proved
open Paper2.Tractable Paper2.ExactInput Paper2.Problem Paper2.RelativeEO
open Paper2.Complexity BinaryCompose FixedFieldMachines FixedFieldOutput
open Paper2.Complexity.UniversalPairReduction.ThreeQuery
open Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.Complexity.UniversalPairReduction
open Holant.Complexity.UniversalPairReduction.Surgery
noncomputable section
set_option backward.isDefEq.respectTransparency false

def pairLabel (L : Language) : Fin (L.count+1) → Fin (L.count+1) :=
  Fin.cases ⟨L.count,Nat.lt_succ_self _⟩ (fun i => i.castSucc)

theorem pairLabel_arity (L : Language) (i : Fin (L.count+1)) :
    extendedArity L.count L.arity (pairLabel L i).val = (tagged L directedPair).arity i.val := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pairLabel,extendedArity]
  · simp [pairLabel,extendedArity,j.isLt,tagged_arity_succ]

theorem pairLabel_marked (L : Language) (i : Fin (L.count+1)) :
    (pairLabel L i).val = L.count ↔ i.val = 0 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [pairLabel]
  · simp [pairLabel,Nat.ne_of_lt j.isLt]

theorem pairLabel_literal (L : Language) (i : Fin (L.count+1)) :
    (⟨extendedArity L.count L.arity (pairLabel L i).val,
      BinaryFamily.signatures (signatures L) BinaryTable.delta (pairLabel L i)⟩ :
      AnySignature AlgebraicComplex) =
        ⟨(tagged L directedPair).arity i.val,(tagged L directedPair).signature i⟩ := by
  refine Fin.cases ?_ (fun j => ?_) i
  · have hz := tagged_zero L directedPair
    apply Eq.trans ?_ hz.symm
    have ha : extendedArity L.count L.arity L.count = 2 := by simp [extendedArity]
    apply Sigma.ext ha
    apply HEq.trans ?_ (heq_of_eq (show
      (fun x : Fin 2 → Bool => BinaryTable.delta (x 0) (x 1)) = directedPair from rfl))
    exact (heq_of_eq (show BinaryFamily.signatures (signatures L) BinaryTable.delta (pairLabel L 0) =
      (fun x => BinaryTable.delta (x (Fin.cast ha.symm 0)) (x (Fin.cast ha.symm 1))) by
      funext x; simp [pairLabel,BinaryFamily.signatures])).trans
      (Holant.Complexity.EdgeSubdivision.signature_cast_heq ha.symm
        (fun x : Fin 2 → Bool => BinaryTable.delta (x 0) (x 1)))
  · have hj := tagged_succ L directedPair j
    apply Eq.trans ?_ hj.symm
    have ha : extendedArity L.count L.arity j.val = L.arity j.val := by simp [extendedArity,j.isLt]
    apply Sigma.ext ha
    exact (heq_of_eq (show BinaryFamily.signatures (signatures L) BinaryTable.delta (pairLabel L j.succ) =
      (fun x => L.signature j (fun k => x (Fin.cast ha.symm k))) by
      funext x; simp [pairLabel,BinaryFamily.signatures,j.isLt,signatures])).trans
      (Holant.Complexity.EdgeSubdivision.signature_cast_heq ha.symm _)

def pairRawInput (L : Language) (G : Instance (tagged L directedPair)) :=
  CanonicalFamily.Relabel.input (pairLabel L) (pairLabel_arity L) (input (tagged L directedPair) G)

theorem pairOccurrences (L : Language) (G : Instance (tagged L directedPair)) :
    Holant.Complexity.FixedGadgetSubstitution.occurrences L.count (pairRawInput L G).val =
      occurrenceCount G.val := by
  have labels : ∀ row ∈ G.val.vertices,
      ((CanonicalFamily.Relabel.row (pairLabel L) row).1 == L.count) = (row.1 == 0) := by
    intro row hr
    have hi := ((Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.RawGrouping.wellFormed_iff_members
      _ _ _ _).mp (input (tagged L directedPair) G).property).1 row hr
    have hi' : row.1 < L.count+1 := by simpa only [tagged_count] using hi.1
    have hh := pairLabel_marked L ⟨row.1,hi'⟩
    apply Bool.eq_iff_iff.mpr
    simpa [CanonicalFamily.Relabel.row,CanonicalFamily.Relabel.label,hi'] using hh
  change ((G.val.vertices.map (CanonicalFamily.Relabel.row (pairLabel L))).filter
    (fun row => row.1 == L.count)).length = (G.val.vertices.filter (fun row => row.1 == 0)).length
  rw [List.filter_map]
  rw [List.length_map]
  apply congrArg List.length
  apply List.filter_congr
  exact labels

def pairInput (L : Language) (G : TaggedInstance L directedPair (fun k => k ≤ 1)) :
    Holant.Complexity.UniversalPairReduction.Input L.count L.arity :=
  ⟨(pairRawInput L G.val).val,(pairRawInput L G.val).property,
    (pairOccurrences L G.val) ▸ G.property⟩

def pairInputComputes (L : Language) :
    Computes (taggedEncoding L directedPair (fun k => k ≤ 1))
      (Holant.Complexity.UniversalPairReduction.inputEncoding L.count L.arity) (pairInput L) :=
  recode (TractableAlgorithms.Paper1Machine.computes
    (CanonicalFamily.Relabel.computes (pairLabel L) (pairLabel_arity L)))
    (fun G => input (tagged L directedPair) G.val)
    (fun G => input_bytes (tagged L directedPair) G.val) (fun _ => rfl)

theorem pairSource_correct (L : Language)
    (G : TaggedInstance L directedPair (fun k => k ≤ 1)) :
    originalEmbedding L (GeneralEOSinglePinSource.sourceValue (signatures L) (pairInput L G)) =
      Problem.value .nativeX (tagged L directedPair) G.val := by
  change (GeneralEOSinglePinSource.sourceValue (signatures L) (pairInput L G) : AlgebraicComplex) = _
  rw [GeneralEOSinglePinSource.source_value_exact,Choice.denote_eq_evaluate]
  let r := input (tagged L directedPair) G.val
  have rows : ∀ i : Fin (L.count+1), ∀ bits,
      Choice.table (signatures (tagged L directedPair)) i.val bits =
      (1 : AlgebraicComplex) * Choice.table
        (BinaryFamily.signatures (signatures L) BinaryTable.delta) (pairLabel L i).val bits := by
    intro i bits
    have he := congrArg (fun f : AnySignature AlgebraicComplex =>
      f.2 (fun j => bits.getD j.val false)) (pairLabel_literal L i)
    simpa [Choice.table,i.isLt,(pairLabel L i).isLt] using he.symm
  have hv := CanonicalFamily.Relabel.value_scaled (pairLabel L)
    (Choice.table (signatures (tagged L directedPair)))
    (Choice.table (BinaryFamily.signatures (signatures L) BinaryTable.delta))
    (fun _ => (1 : AlgebraicComplex)) (pairLabel_arity L) r rows
  have ones : RootPreprocessing.OccurrenceProduct.value
      (fun _ : Fin (L.count+1) => (1 : AlgebraicComplex)) r.val = 1 := by
    unfold RootPreprocessing.OccurrenceProduct.value
    have hm : r.val.vertices.map (fun row => RootPreprocessing.OccurrenceProduct.total
        (fun _ : Fin (L.count+1) => (1 : AlgebraicComplex)) row.1) =
        r.val.vertices.map (fun _ => (1 : AlgebraicComplex)) := by
      apply List.map_congr_left
      intro row hr
      have hi := ((Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.RawGrouping.wellFormed_iff_members
        _ _ _ _).mp r.property).1 row hr
      have hi' : row.1 < L.count+1 := by simpa only [tagged_count] using hi.1
      simp [RootPreprocessing.OccurrenceProduct.total,hi']
    rw [hm]
    simp
  rw [ones,one_mul] at hv
  have hs := network_value .nativeX (tagged L directedPair) G.val
  rw [show Paper2.Paper1Proved.kernels .nativeX =
    (fun _ : Fin 1 => Holant.Signature.disequality) from rfl] at hs
  rw [Choice.denote_eq_evaluate] at hs
  exact hv.symm.trans hs

theorem universalPair (L : Language) :
    FixedFieldOutput.TaggedReduces .nativeX L directedPair (fun k => k ≤ 1) L := by
  let source := tagged L directedPair
  let r := GeneralEOSinglePinSource.source (signatures L)
  let q := pairInput L
  let pre := pairInputComputes L
  let size := (controlledReduction r).sourceOutputBound
  let f := GeneralEOSinglePinSource.sourceValue (signatures L)
  let pre3 := pairComputes pre (pairComputes pre (pairComputes pre
    (constantComputes (taggedEncoding L directedPair (fun k => k ≤ 1)) Computability.encodingBoolBool false)))
  let first := Wiring.firstComputes (originalPresentation L).encoding
    (pairEncoding (originalPresentation L).encoding
      (pairEncoding (originalPresentation L).encoding Computability.encodingBoolBool))
  let post := first.andThen (forwardFieldConversion source (originalPresentation L) (originalEmbedding L))
  have outer : LengthControlledOracleReduction
      (taggedEncoding L directedPair (fun k => k ≤ 1)) (answerEncoding source)
      (Holant.Complexity.UniversalPairReduction.inputEncoding L.count L.arity)
      (originalPresentation L).encoding (taggedAnswer .nativeX L directedPair (fun k => k ≤ 1)) f := by
    apply controlledOfEq pre3 post size (taggedAnswer .nativeX L directedPair (fun k => k ≤ 1))
    intro G
    symm
    apply TractableAlgorithms.Paper1Machine.coordinates_correct source
      ((originalEmbedding L).comp (originalPresentation L).decode.toLinearMap) _ .nativeX G.val
    simpa only [answers,LinearMap.comp_apply,LinearEquiv.coe_coe,
      LinearEquiv.apply_symm_apply] using pairSource_correct L G
  exact ⟨outer.controlledCompose ((controlledReduction r).controlledCompose
    (fieldTargetReduction .nativeX L (originalPresentation L) (originalEmbedding L)
      Subtype.val_injective (originalValue L) (originalEmbedding_correct L)))⟩

end
end Paper2.Paper1Proved
