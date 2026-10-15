import Paper2.Paper1ProvedOddResiduePins
import Paper2.Paper1ProvedFactorProvider
import Holant.Proofs.Hardness.GeneralEOSinglePinAmplificationProgramme

/-! The alternating EO four-port residue supplies virtual directed pins by
the actual anchored three-query programme. Its finite original-field answer
codec is converted at both canonical endpoints; no pure equality resource is
inferred from the alternating table. -/
namespace Paper2.Paper1Proved.OddResidue
noncomputable section
open Computability Paper2.Tractable Paper2.ExactInput Paper2.RelativeEO
open Holant.Complexity Holant.Complexity.UniversalPairReduction
open Holant.LocalDrafts.Hardness.GeneralExtraction
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1400000

namespace Amplification
variable (L : Language)
abbrev field := originalField L
local instance : Algebra ℚ (field L) := (field L).algebra'
abbrev presentation := originalPresentation L
abbrev tables := GeneralOriginalTarget.originalTables (signatures L)
abbrev rows := ValueJoins.signatures (presentation L) (tables L)
abbrev extended := BinaryFamily.signatures (signatures L) BinaryTable.delta

@[simp] theorem row_coe (i : Fin L.count) (x : Fin (L.arity i.val) → Bool) :
    (rows L i x : AlgebraicComplex) = L.signature i x := by
  simp only [rows,ValueJoins.signatures,tables,GeneralOriginalTarget.originalTables,
    LinearEquiv.apply_symm_apply]
  rfl

theorem native : ∀ i b c,(presentation L).decode ((tables L).edge i b c) =
    Holant.Signature.disequality b c := by
  intro i b c
  simp only [tables,GeneralOriginalTarget.originalTables,LinearEquiv.apply_symm_apply]

theorem extended_family : Set.range (fun i : Fin (L.count+1) =>
    (⟨extendedArity L.count L.arity i.val,extended L i⟩ : AnySignature AlgebraicComplex)) =
    insert ⟨2,directedPair⟩ L.family := by
  ext g
  constructor
  · rintro ⟨i,rfl⟩
    by_cases hi : i.val < L.count
    · right
      refine ⟨⟨i.val,hi⟩,?_⟩
      have ha : extendedArity L.count L.arity i.val = L.arity i.val := by
        simp [extendedArity,hi]
      apply Eq.symm
      apply Sigma.ext ha
      exact (heq_of_eq (show extended L i =
        (fun x => L.signature ⟨i.val,hi⟩ (fun k => x (Fin.cast ha.symm k))) by
          funext x; simp [extended,BinaryFamily.signatures,hi,signatures])).trans
        (Holant.Complexity.EdgeSubdivision.signature_cast_heq ha.symm _)
    · left
      have he : i = ⟨L.count,Nat.lt_succ_self _⟩ := by
        apply Fin.ext
        change i.val = L.count
        have := i.isLt
        omega
      subst i
      have ha : extendedArity L.count L.arity L.count = 2 := by simp [extendedArity]
      apply Sigma.ext ha
      exact (heq_of_eq (show extended L ⟨L.count,Nat.lt_succ_self _⟩ =
        (fun x => directedPair (fun k => x (Fin.cast ha.symm k))) by
          funext x; simp [extended,BinaryFamily.signatures,directedPair,BinaryTable.delta])).trans
        (Holant.Complexity.EdgeSubdivision.signature_cast_heq ha.symm _)
  · rintro (rfl | ⟨i,rfl⟩)
    · refine ⟨⟨L.count,Nat.lt_succ_self _⟩,?_⟩
      have ha : extendedArity L.count L.arity L.count = 2 := by simp [extendedArity]
      apply Sigma.ext ha
      exact (heq_of_eq (show extended L ⟨L.count,Nat.lt_succ_self _⟩ =
        (fun x => directedPair (fun k => x (Fin.cast ha.symm k))) by
          funext x; simp [extended,BinaryFamily.signatures,directedPair,BinaryTable.delta])).trans
        (Holant.Complexity.EdgeSubdivision.signature_cast_heq ha.symm _)
    · refine ⟨i.castSucc,?_⟩
      have ha : extendedArity L.count L.arity i.val = L.arity i.val := by
        simp [extendedArity,i.isLt]
      apply Sigma.ext ha
      exact (heq_of_eq (show extended L i.castSucc =
        (fun x => L.signature i (fun k => x (Fin.cast ha.symm k))) by
          funext x; simp [extended,BinaryFamily.signatures,i.isLt,signatures])).trans
        (Holant.Complexity.EdgeSubdivision.signature_cast_heq ha.symm _)

theorem map_extended (i : Fin (L.count+1))
    (x : Fin (extendedArity L.count L.arity i.val) → Bool) :
    ((BinaryFamily.signatures (rows L) BinaryTable.delta i x : field L) :
      AlgebraicComplex) = extended L i x := by
  simp only [BinaryFamily.signatures,extended]
  split_ifs with hi
  · exact row_coe L _ _
  · simp only [BinaryTable.delta]
    split_ifs <;> rfl

theorem source_exact
    (r : GeneralEOSinglePinAmplificationProgramme.Input (s:=L.count) (a:=L.arity)) :
    ((GeneralEOSinglePinAmplificationProgramme.sourceValue (presentation L) (tables L) r :
      field L) : AlgebraicComplex) =
    (r.val.realize r.property (extended L)
      (fun _ => Holant.Signature.disequality)).denote Fin.elim0 := by
  change (field L).subtype
    ((r.val.realize r.property (BinaryFamily.signatures (rows L) BinaryTable.delta)
      (fun _ => Holant.Signature.disequality)).denote Fin.elim0) = _
  rw [← Holant.Network.denote_map (field L).subtype]
  congr 1
  unfold Holant.Network.map Holant.Complexity.RawClosedNetwork.realize
  congr 1
  · funext v x
    exact map_extended L _ _
  · funext e a b
    cases a <;> cases b <;> rfl

theorem field_E (j : Fin L.count)
    (hj : (⟨L.arity j.val,L.signature j⟩ : AnySignature AlgebraicComplex) =
      ⟨4,ExactTwoSignatures.E⟩) :
    (⟨L.arity j.val,rows L j⟩ : AnySignature (field L)) =
      ⟨4,ExactTwoSignatures.E⟩ := by
  have ha : L.arity j.val = 4 := congrArg Sigma.fst hj
  apply Sigma.ext ha
  apply HEq.trans ?_ (Holant.Complexity.EdgeSubdivision.signature_cast_heq ha.symm
    (ExactTwoSignatures.E : Holant.Signature (field L) 4))
  apply heq_of_eq
  funext x
  apply Subtype.ext
  rw [row_coe]
  have he := Holant.Complexity.BinaryInterpolation.Chains.signature_cast_apply
    (L.signature j) ExactTwoSignatures.E hj ha (fun k => x (Fin.cast ha.symm k))
  have hx : (fun i => x (Fin.cast ha.symm (Fin.cast ha i))) = x := by
    funext i
    simp
  rw [hx] at he
  rw [he]
  rw [ExactTwoSignatures.E_reference,ExactTwoSignatures.E_reference]
  split_ifs <;> rfl

end Amplification

/-- Arbitrarily many directed-pair occurrences are removed by the proved
anchored programme when the actual alternating four-port row is present. -/
theorem literal_E_directed_pair (L : Language)
    (hE : (⟨4,ExactTwoSignatures.E⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ M : Language,M.family = insert ⟨2,directedPair⟩ L.family ∧
      FixedFieldOutput.Reduces .nativeX M L := by
  let : Algebra ℚ (originalField L) := (originalField L).algebra'
  obtain ⟨M,hM⟩ := Language.coverage_family (insert ⟨2,directedPair⟩ L.family)
    (L.family_finite.insert _)
  have hsub : M.family ⊆ Set.range (fun i : Fin (L.count+1) =>
      (⟨extendedArity L.count L.arity i.val,Amplification.extended L i⟩ :
        AnySignature AlgebraicComplex)) := by
    rw [Amplification.extended_family,hM]
  obtain ⟨j,hj⟩ := hE
  let F := Amplification.presentation L
  let T := Amplification.tables L
  let f := GeneralEOSinglePinAmplificationProgramme.sourceValue F T
  let q := FactorProvider.sourceInput (Amplification.extended L) M hsub
  let r := GeneralEOSinglePinAmplificationProgramme.source F T
    (Amplification.native L) j (Amplification.field_E L j hj)
  refine ⟨M,hM,⟨canonicalReduction .nativeX .nativeX M L
    (GeneralEOSinglePinAmplificationProgramme.inputEncoding (s:=L.count) (a:=L.arity))
    F (originalEmbedding L) f q
    (FactorProvider.sourceComputes (Amplification.extended L) M hsub)
    ?_ F (originalEmbedding L) Subtype.val_injective (originalValue L)
    (originalEmbedding_correct L) r⟩⟩
  intro G
  exact (Amplification.source_exact L (q G)).trans
    (FactorProvider.sourceDenote (Amplification.extended L) M hsub G)

/-- A true scalar alternating EO graph supplies oracle access to both unit
pins through macro installation, the three-query amplifier, and factor
extraction. Every old row is retained in the final language. -/
theorem alternating_E_pins
    (G : SourceFaithful.Paper1DirectGadgetAccepted)
    (R : SourceFaithful.Paper1RestrictionAccepted)
    (Fac : SourceFaithful.Paper1FactorClosureAccepted)
    (L : Language) (hp : Preprocessed L.family) (hs : ¬ CommonOneSided L.family)
    (c : AlgebraicComplex) (hc : c ≠ 0)
    (hgraph : NetworkRealizable L.family (c • ExactTwoSignatures.E)) :
    ∃ M : Language,L.family ⊆ M.family ∧
      (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ M.family ∧
      Preprocessed M.family ∧ ¬ CommonOneSided M.family ∧
      FixedFieldOutput.Reduces .nativeX M L ∧ FixedFieldOutput.Reduces .nativeX L M := by
  obtain ⟨N,hN,hX,hval⟩ := hgraph.ordered
  obtain ⟨A,hA,hAL,hLA⟩ := G.adjoin_equivalence R L ExactTwoSignatures.E
    ⟨N,hN,hX,c,hc,hval⟩
  have hsub : L.family ⊆ A.family := by rw [hA]; exact Set.subset_insert _ _
  have hmem : (⟨4,ExactTwoSignatures.E⟩ : AnySignature AlgebraicComplex) ∈ A.family := by
    rw [hA]
    exact Set.mem_insert _ _
  obtain ⟨B,hB,hBA⟩ := literal_E_directed_pair A hmem
  have hAB : A.family ⊆ B.family := by rw [hB]; exact Set.subset_insert _ _
  have hpA : Preprocessed A.family := by
    rw [hA]
    rintro f (rfl | hf)
    · refine ⟨by decide,?_⟩
      intro hz
      have hh := congrFun hz ![false,true,false,true]
      simpa [ExactTwoSignatures.E_reference] using hh
    · exact hp f hf
  have hpB : Preprocessed B.family := by
    rw [hB]
    rintro f (rfl | hf)
    · refine ⟨by decide,?_⟩
      intro hz
      have hh := congrFun hz ![false,true]
      simp [directedPair] at hh
    · exact hpA f hf
  have hsB : ¬ CommonOneSided B.family := by
    intro h
    exact hs (h.mono_family (hsub.trans hAB))
  have hpair : (⟨2,directedPair⟩ : AnySignature AlgebraicComplex) ∈ B.family := by
    rw [hB]
    exact Set.mem_insert _ _
  obtain ⟨M,hBM,h0,h1,hpM,hsM,hMB,hBMred⟩ :=
    SourceFaithful.RelativeEO.directedPair_factorClosure Fac B hpB hsB hpair
  have hLAB : FixedFieldOutput.Reduces .nativeX L B :=
    hLA.trans (R.restriction_2_5 A B hAB)
  exact ⟨M,hsub.trans (hAB.trans hBM),h0,h1,hpM,hsM,
    hMB.trans (hBA.trans hAL),hLAB.trans hBMred⟩

end
end Paper2.Paper1Proved.OddResidue
