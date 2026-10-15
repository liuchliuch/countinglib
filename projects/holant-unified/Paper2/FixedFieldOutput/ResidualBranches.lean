import Paper2.FixedFieldOutput.ResidualRawPlans
import Paper2.FixedFieldOutput.TwoBellReductions
import Paper2.BellReduction.OneOccurrence

/-! Concrete original-graph 0/1/2 Bell branches. Each branch combines an actual
raw precompiler with valid original-language queries and its exact value proof. -/
namespace Paper2.FixedFieldOutput.ResidualBranches
open Computability Paper2.Complexity BinaryCompose FixedFieldMachines BellMachines
open Paper2.ExactInput Paper2.Problem Paper2.Tractable Paper2.RelativeEO
open UniversalPairReduction.ThreeQuery BellPostprocessing ResidualCompiler
open Paper2.BellReduction
noncomputable section

 def noFlags : Flags := ((false,false),(false,false),(false,false))

 theorem subset_tagged (L : Language) (g : Signature AlgebraicComplex 2) :
    L.family ⊆ (tagged L g).family := by
  rw [tagged_family]
  exact Set.subset_insert _ _

 theorem post_zero (L : Language) (g : Signature AlgebraicComplex 2) (p : Plan L) :
    ((tagged L g).fieldPresentation.decode
      (post L (tagged L g) (fun _ => 0) (answers (answer .nativeX L) p)) : AlgebraicComplex) = 0 := by
  have h := post_correct L (tagged L g) (subset_tagged L g) (fun _ => 0)
    ![p.1,p.2.1,p.2.2.1] p.2.2.2
  simpa [answers] using h

 theorem post_first (L : Language) (g : Signature AlgebraicComplex 2) (q : Instance L) :
    ((tagged L g).fieldPresentation.decode
      (post L (tagged L g) ![1,0,0]
        (answer .nativeX L q,answer .nativeX L q,answer .nativeX L q,noFlags)) : AlgebraicComplex) =
      value .nativeX L q := by
  have h := post_correct L (tagged L g) (subset_tagged L g) ![1,0,0] (fun _ => q) noFlags
  simpa [readFlag,noFlags,pairFactor,flag] using h


 def zero (L : Language) (g : Signature AlgebraicComplex 2) : Branch L g 0 where
  raw := ResidualRawPlans.zero
  computes := ResidualRawPlans.zeroComputes
  plan := ResidualRawPlans.zeroPlan L g
  raw_spec := ResidualRawPlans.zero_spec L g
  coeff := ![1,0,0]
  correct G := (post_first L g (DropTag.input L g G)).trans (DropTag.value L g G)

 def twoY (L : Language) : Branch L (bellTable true true) 2 where
  raw := ResidualRawPlans.closures
  computes := ResidualRawPlans.closuresComputes
  plan := ClosureQueries.pre L (bellTable true true)
  raw_spec := ResidualRawPlans.closures_spec L (bellTable true true)
  coeff := twoYCoefficients (tagged L (bellTable true true))
  correct G := by
    rw [TwoBellReductions.post_query_value,OriginalQueries.two_y L G.val G.property]
    change OriginalQueries.weightedQuery L (bellTable true true) G.val G.property 0 * (0:AlgebraicComplex) +
      OriginalQueries.weightedQuery L (bellTable true true) G.val G.property 1 * (-1:AlgebraicComplex) +
      OriginalQueries.weightedQuery L (bellTable true true) G.val G.property 2 * (1:AlgebraicComplex) = _
    ring

 def twoI (L : Language) (hHigh : HighCharge L.family) : Branch L (bellTable false false) 2 where
  raw := ResidualRawPlans.closures
  computes := ResidualRawPlans.closuresComputes
  plan := ClosureQueries.pre L (bellTable false false)
  raw_spec := ResidualRawPlans.closures_spec L (bellTable false false)
  coeff := twoICoefficients (tagged L (bellTable false false))
  correct G := by
    rw [TwoBellReductions.post_query_value]
    have h := OriginalQueries.two_i L hHigh G.val G.property
    change OriginalQueries.weightedQuery L (bellTable false false) G.val G.property 0 * (-(2:AlgebraicComplex)⁻¹) +
      OriginalQueries.weightedQuery L (bellTable false false) G.val G.property 1 * (2:AlgebraicComplex)⁻¹ +
      OriginalQueries.weightedQuery L (bellTable false false) G.val G.property 2 * (2:AlgebraicComplex)⁻¹ = _
    linear_combination -(1/2 : AlgebraicComplex) * h

 def oneI (L : Language) (hHigh : HighCharge L.family) : Branch L (bellTable false false) 1 where
  raw := fun _ => ResidualRawPlans.empty
  computes := ResidualRawPlans.emptyComputes
  plan := fun _ => ResidualRawPlans.emptyPlan L
  raw_spec := fun _ => ResidualRawPlans.empty_spec L
  coeff := fun _ => 0
  correct G := (post_zero L _ _).trans (OriginalQueries.one_i L hHigh G.val G.property).symm

 def oneYZero (L : Language)
    (h : ¬ ∃ W : Instance (tagged L (bellTable true true)),
      RawOccurrence.markedCount W.val.vertices = 1 ∧ value .nativeX (tagged L (bellTable true true)) W ≠ 0) :
    Branch L (bellTable true true) 1 where
  raw := fun _ => ResidualRawPlans.empty
  computes := ResidualRawPlans.emptyComputes
  plan := fun _ => ResidualRawPlans.emptyPlan L
  raw_spec := fun _ => ResidualRawPlans.empty_spec L
  coeff := fun _ => 0
  correct G := (post_zero L _ _).trans (OriginalQueries.one_y_zero_of_no_witness L h G.val G.property).symm

 def witnessInput (L : Language) (W : Instance (tagged L (bellTable true true)))
    (hW : RawOccurrence.markedCount W.val.vertices = 1)
    (G : TaggedInstance L (bellTable true true) (fun k => k = 1)) :
    TaggedInstance L (bellTable true true) (fun k => k = 2) :=
  ⟨OriginalQueries.witnessUnion L G.val W,OriginalQueries.witnessUnion_count L G.val W G.property hW⟩

 def witnessValue (L : Language) (W : Instance (tagged L (bellTable true true))) :
    (tagged L (bellTable true true)).coefficientField :=
  (fieldNetwork .nativeX (tagged L (bellTable true true)) W).denote Fin.elim0

 theorem witnessValue_coe (L : Language) (W : Instance (tagged L (bellTable true true))) :
    (witnessValue L W : AlgebraicComplex) = value .nativeX (tagged L (bellTable true true)) W :=
  fieldNetwork_value .nativeX (tagged L (bellTable true true)) W

 def oneYWitness (L : Language) (W : Instance (tagged L (bellTable true true)))
    (hW : RawOccurrence.markedCount W.val.vertices = 1)
    (hne : value .nativeX (tagged L (bellTable true true)) W ≠ 0) :
    Branch L (bellTable true true) 1 where
  raw := ResidualRawPlans.witness W.val
  computes := ResidualRawPlans.witnessComputes W.val
  plan := fun G => ClosureQueries.pre L (bellTable true true) (witnessInput L W hW G)
  raw_spec G := ResidualRawPlans.closures_spec L (bellTable true true) (witnessInput L W hW G)
  coeff := ![0,-(witnessValue L W)⁻¹,(witnessValue L W)⁻¹]
  correct G := by
    rw [TwoBellReductions.post_query_value]
    change OriginalQueries.weightedQuery L (bellTable true true) (OriginalQueries.witnessUnion L G.val W)
        (OriginalQueries.witnessUnion_count L G.val W G.property hW) 0 * (0:AlgebraicComplex) +
      OriginalQueries.weightedQuery L (bellTable true true) (OriginalQueries.witnessUnion L G.val W)
        (OriginalQueries.witnessUnion_count L G.val W G.property hW) 1 * (-(witnessValue L W : AlgebraicComplex)⁻¹) +
      OriginalQueries.weightedQuery L (bellTable true true) (OriginalQueries.witnessUnion L G.val W)
        (OriginalQueries.witnessUnion_count L G.val W G.property hW) 2 * (witnessValue L W : AlgebraicComplex)⁻¹ = _
    rw [witnessValue_coe,OriginalQueries.one_y_queries L W hW hne G.val G.property]
    ring

def branchCases {L : Language} {g : Signature AlgebraicComplex 2}
    (b0 : Branch L g 0) (b1 : Branch L g 1) (b2 : Branch L g 2) :
    ∀ i : Fin 3, Branch L g i :=
  fun i => Fin.cases b0 (fun j => Fin.cases b1 (fun k => Fin.cases b2 (fun z => Fin.elim0 z) k) j) i

/-- Every Y branch is supplied by an actual compiler. The fixed-witness choice
is nonuniform only in the fixed language, never in a graph input or runtime. -/
 def branchesY (L : Language) : ∀ i : Fin 3, Branch L (bellTable true true) i := by
  classical
  by_cases h : ∃ W : Instance (tagged L (bellTable true true)),
      RawOccurrence.markedCount W.val.vertices = 1 ∧ value .nativeX (tagged L (bellTable true true)) W ≠ 0
  · let W := Classical.choose h
    have hs := Classical.choose_spec h
    exact branchCases (zero L _) (oneYWitness L W hs.1 hs.2) (twoY L)
  · exact branchCases (zero L _) (oneYZero L h) (twoY L)

 def branchesI (L : Language) (hHigh : HighCharge L.family) :
    ∀ i : Fin 3, Branch L (bellTable false false) i :=
  branchCases (zero L _) (oneI L hHigh) (twoI L hHigh)

end
end Paper2.FixedFieldOutput.ResidualBranches
