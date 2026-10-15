import Paper2.FixedFieldOutput.BellReductions
import Paper2.BellReduction.BellAdjunction
import Paper2.SourceFaithful.LocalInputs
import Paper2.Tractable.CriteriaFacts

/-! Original-language RM8/Bell terminal. The Bell adjunction reductions below
are actual proved finite-machine reductions, not accepted Paper2 inputs. Only
the literal-equality Paper1 classification is an explicit source parameter. -/
namespace Paper2.SourceFaithful.BellTerminal
open Tractable ExactInput RelativeEO BellReduction

 theorem core_highCharge (c : AlgebraicComplex) :
    Even (8 : ℕ) ∧ Tensor.HalfChargeDivisible (fun x => c * ReedMuller.core x) 4 := by
  refine ⟨by decide,?_⟩
  intro x hx
  have hcode : ReedMuller.IsCodeword x := by
    by_contra hn
    exact hx (by simp [ReedMuller.core,hn])
  have hw : Paper2.weight x = ReedMuller.weight x := by
    apply Finset.sum_congr rfl
    intro i _
    cases x i <;> rfl
  have hh := ReedMuller.codeword_weight x hcode
  simp only [halfCharge,Fintype.card_fin,hw]
  rcases hh with hh | hh | hh <;> rw [hh] <;> norm_num

/-- The two literal labels used by the equality-hardness route. Each has a
fresh index even when its table already occurs in the original language. -/
noncomputable def equalityExtension (L : Language) : Language :=
  tagged (tagged L (bellTable true true)) (bellTable false false)

/-- The entire ordered Bell dictionary, including the two direct-path labels.
All original signature codes remain literally in this finite language. -/
noncomputable def bellExtension (L : Language) : Language :=
  tagged (tagged (equalityExtension L) (bellTable true false)) (bellTable false true)

 theorem equalityExtension_family (L : Language) :
    (equalityExtension L).family =
      insert (⟨2,bellTable false false⟩ : AnySignature AlgebraicComplex)
        (insert (⟨2,bellTable true true⟩ : AnySignature AlgebraicComplex) L.family) := by
  simp [equalityExtension]

 theorem bellExtension_family (L : Language) :
    (bellExtension L).family =
      insert (⟨2,bellTable false true⟩ : AnySignature AlgebraicComplex)
        (insert (⟨2,bellTable true false⟩ : AnySignature AlgebraicComplex)
          (insert (⟨2,bellTable false false⟩ : AnySignature AlgebraicComplex)
            (insert (⟨2,bellTable true true⟩ : AnySignature AlgebraicComplex) L.family))) := by
  simp [bellExtension,equalityExtension]

 theorem bellExtension_contains (L : Language) (d l : Bool) :
    (⟨2,bellTable d l⟩ : AnySignature AlgebraicComplex) ∈ (bellExtension L).family := by
  cases d <;> cases l <;> simp [bellExtension_family]

/-- All four ordered two-port Bell truth tables in the printed dictionary. -/
def bellFamily : SignatureFamily AlgebraicComplex :=
  Set.range (fun p : Bool × Bool => (⟨2,bellTable p.1 p.2⟩ : AnySignature AlgebraicComplex))

 theorem bellExtension_family_union (L : Language) :
    (bellExtension L).family = L.family ∪ bellFamily := by
  ext f
  constructor
  · intro hf
    rw [bellExtension_family] at hf
    rcases hf with rfl | rfl | rfl | rfl | hf
    · exact Or.inr ⟨(false,true),rfl⟩
    · exact Or.inr ⟨(true,false),rfl⟩
    · exact Or.inr ⟨(false,false),rfl⟩
    · exact Or.inr ⟨(true,true),rfl⟩
    · exact Or.inl hf
  · rintro (hf | ⟨⟨d,l⟩,rfl⟩)
    · rw [bellExtension_family]
      exact Or.inr (Or.inr (Or.inr (Or.inr hf)))
    · exact bellExtension_contains L d l

/-- Q8.33 and Q8.35 composed as actual encoded finite-machine reductions. -/
theorem equalityExtension_reduces (L : Language) (hHigh : HighCharge L.family)
    (c : AlgebraicComplex) (hc : c ≠ 0)
    (hcore : (⟨8,fun x => c * ReedMuller.core x⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    FixedFieldOutput.Reduces .nativeX (equalityExtension L) L := by
  let YL := tagged L (bellTable true true)
  have hsub : L.family ⊆ YL.family := by
    dsimp only [YL]
    rw [tagged_family]
    exact Set.subset_insert _ _
  have hhighY : HighCharge YL.family := by
    dsimp only [YL]
    rw [tagged_family]
    exact highCharge_insert_y hHigh
  exact (FixedFieldOutput.BellReductions.I YL hhighY c hc (hsub hcore)).trans
    (FixedFieldOutput.BellReductions.Y L c hc hcore)

/-- Source Lemma 8.12, Q8.31: the complete finite Bell extension reduces to the
original language. I and Y use the proved multi-query machines; X and Z use
literal one-edge two-vertex native gadgets and only the original direct-gadget
reduction lemma. No Bell compiler or runtime bound is a caller premise. -/
theorem bellExtension_reduces (DG : Paper1DirectGadgetAccepted)
    (L : Language) (hHigh : HighCharge L.family)
    (c : AlgebraicComplex) (hc : c ≠ 0)
    (hcore : (⟨8,fun x => c * ReedMuller.core x⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    FixedFieldOutput.Reduces .nativeX (bellExtension L) L := by
  let IL := equalityExtension L
  have hI : (⟨2,bellTable false false⟩ : AnySignature AlgebraicComplex) ∈ IL.family := by
    simp [IL,equalityExtension_family]
  have hY : (⟨2,bellTable true true⟩ : AnySignature AlgebraicComplex) ∈ IL.family := by
    simp [IL,equalityExtension_family]
  have hfamily : (bellExtension L).family =
      insert (⟨2,bellTable false true⟩ : AnySignature AlgebraicComplex)
        (insert (⟨2,bellTable true false⟩ : AnySignature AlgebraicComplex) IL.family) := by
    simp [bellExtension,IL]
  have hsub : IL.family ⊆ (bellExtension L).family := by
    rw [hfamily]
    exact (Set.subset_insert _ _).trans (Set.subset_insert _ _)
  have hgadget : FixedFieldOutput.Reduces .nativeX (bellExtension L) IL :=
    DG.directGadget_2_5 IL (bellExtension L) hsub (by
      intro f hf
      rw [hfamily] at hf
      rcases hf with rfl | rfl | hf
      · exact NativeNetworkRealizesUpTo.of_realizable (BellAdjunction.z_realizable hI hY)
      · exact NativeNetworkRealizesUpTo.of_realizable (BellAdjunction.x_realizable hI)
      · exact NativeNetworkRealizesUpTo.of_mem hf)
  exact hgadget.trans (equalityExtension_reduces L hHigh c hc hcore)

/-- The literal finite-language form of Q8.31. This existential packages
only the input-language codes; its reduction already executes all graph,
oracle and canonical field-answer stages. -/
theorem bell_reduction (DG : Paper1DirectGadgetAccepted)
    (L : Language) (hHigh : HighCharge L.family)
    (c : AlgebraicComplex) (hc : c ≠ 0)
    (hcore : (⟨8,fun x => c * ReedMuller.core x⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    ∃ M : Language, M.family = L.family ∪ bellFamily ∧
      FixedFieldOutput.Reduces .nativeX M L :=
  ⟨bellExtension L,bellExtension_family_union L,bellExtension_reduces DG L hHigh c hc hcore⟩

/-- Source Lemma 8.12 closes in the original literal language once its nonzero
RM8 core is present. The equality oracle is reached through both proven Bell
adjunction machines, retaining all original graph and answer encodings. -/
theorem rm8_hard (P : Paper1Accepted) (L : Language)
    (hHigh : HighCharge L.family) (hnot : ¬ Tract (kImage L))
    (c : AlgebraicComplex) (hc : c ≠ 0)
    (hcore : (⟨8,fun x => c * ReedMuller.core x⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  let YL := tagged L (bellTable true true)
  let IL := tagged YL (bellTable false false)
  have hLY : L.family ⊆ YL.family := by
    dsimp only [YL]
    rw [tagged_family]
    exact Set.subset_insert _ _
  have hYI : YL.family ⊆ IL.family := by
    simpa only [IL,tagged_family] using
      (Set.subset_insert (⟨2,bellTable false false⟩ : AnySignature AlgebraicComplex) YL.family)
  have hY : HighCharge YL.family := by
    dsimp only [YL]
    rw [tagged_family]
    exact highCharge_insert_y hHigh
  have heq : HasLiteralEquality IL := by
    unfold HasLiteralEquality
    dsimp only [IL]
    rw [tagged_family]
    left
    congr 1
    funext x
    change Signature.equality (x 0) (x 1) = Bell.I (x 0) (x 1)
    rw [Bell.I_eq_equality]
  have hn : ¬ Tract (kImage IL) := by
    intro ht
    exact hnot (ht.mono_family (familyAction_mono sourceKBasis (hLY.trans hYI)))
  have hh := (P.literalEqualityDichotomy_2_23 IL heq).2 hn
  have rY := FixedFieldOutput.BellReductions.Y L c hc hcore
  have rI := FixedFieldOutput.BellReductions.I YL hY c hc (hLY hcore)
  exact hh.transport (rI.trans rY)

 theorem rm8_classification (P : Paper1Accepted) (L : Language)
    (hHigh : HighCharge L.family) (c : AlgebraicComplex) (hc : c ≠ 0)
    (hcore : (⟨8,fun x => c * ReedMuller.core x⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    Tract (kImage L) ∨ FixedFieldOutput.SharpPHard .nativeX L := by
  classical
  by_cases ht : Tract (kImage L)
  · exact Or.inl ht
  · exact Or.inr (rm8_hard P L hHigh ht c hc hcore)

/-- A realized RM8 signature is adjoined only through its actual native graph;
the entire retained original family and its hardness are transported back. -/
theorem realized_rm8_hard (P : Paper1Accepted) (DG : Paper1DirectGadgetAccepted)
    (L : Language) (hHigh : HighCharge L.family) (hnot : ¬ Tract (kImage L))
    (c : AlgebraicComplex) (hc : c ≠ 0)
    (hcore : NetworkRealizable L.family (fun x : Fin 8 → Bool => c * ReedMuller.core x)) :
    FixedFieldOutput.SharpPHard .nativeX L := by
  obtain ⟨M,hM,hML⟩ := DG.adjoin_realizable L _ hcore
  have hsub : L.family ⊆ M.family := by rw [hM]; exact Set.subset_insert _ _
  have hhighM : HighCharge M.family := by
    rw [hM]
    intro f hf
    rcases hf with rfl | hf
    · exact core_highCharge c
    · exact hHigh f hf
  have hnotM : ¬ Tract (kImage M) := by
    intro ht
    exact hnot (ht.mono_family (familyAction_mono sourceKBasis hsub))
  exact (rm8_hard P M hhighM hnotM c hc (by rw [hM]; exact Set.mem_insert _ _)).transport hML

end Paper2.SourceFaithful.BellTerminal

