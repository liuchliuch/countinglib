import Paper2.FixedFieldOutput.ResidualCompiler
import Paper2.FixedFieldOutput.ClosureQueries
import Paper2.FixedFieldOutput.TwoBellReductions
import Paper2.Complexity.BellMachines.FixedUnionCompile

/-! Concrete raw candidate precompilers for the residual occurrence dispatch.
Candidates may be arbitrary on the wrong branch; `Branch.raw_spec` establishes
that the selected branch always emits valid original-language queries. -/
namespace Paper2.FixedFieldOutput.ResidualRawPlans
open Computability Paper2.Complexity BinaryCompose FixedFieldMachines BellMachines
open GraphPreprocessing UniversalPairReduction.ThreeQuery
open Paper2.ExactInput Paper2.Problem Paper2.Tractable Paper2.RelativeEO
open BellPostprocessing ResidualCompiler
noncomputable section

 def zero (G : RawClosedNetwork) : RawPlan :=
  (DropTag.raw G,DropTag.raw G,DropTag.raw G,(false,false),(false,false),(false,false))
 def zeroComputes : Computes RawClosedNetwork.encoding rawPlanEncoding zero :=
  pairComputes DropTag.rawComputes (pairComputes DropTag.rawComputes
    (pairComputes DropTag.rawComputes
      (constantComputes RawClosedNetwork.encoding flagsEncoding ((false,false),(false,false),(false,false)))))

 def zeroPlan (L : Language) (g : Signature AlgebraicComplex 2)
    (G : TaggedInstance L g (fun k => k = 0)) : Plan L :=
  (DropTag.input L g G,DropTag.input L g G,DropTag.input L g G,
    (false,false),(false,false),(false,false))
 theorem zero_spec (L : Language) (g : Signature AlgebraicComplex 2)
    (G : TaggedInstance L g (fun k => k = 0)) : zero G.val.val = toRaw (zeroPlan L g G) := rfl

 def emptyRaw : RawClosedNetwork := ⟨[],[]⟩
 def emptyInput (L : Language) : Instance L := ⟨emptyRaw,by
   refine ⟨?_,?_,List.Perm.nil⟩
   · intro v; exact Fin.elim0 v
   · intro e; exact Fin.elim0 e⟩
 def emptyPlan (L : Language) : Plan L :=
  (emptyInput L,emptyInput L,emptyInput L,(false,false),(false,false),(false,false))
 def empty : RawPlan :=
  (emptyRaw,emptyRaw,emptyRaw,(false,false),(false,false),(false,false))
 def emptyComputes : Computes RawClosedNetwork.encoding rawPlanEncoding (fun _ => empty) :=
  constantComputes RawClosedNetwork.encoding rawPlanEncoding empty
 theorem empty_spec (L : Language) : empty = toRaw (emptyPlan L) := rfl

 def closures (G : RawClosedNetwork) : RawPlan :=
  ((ClosureQueries.rawOutput 0 G).1,(ClosureQueries.rawOutput 1 G).1,(ClosureQueries.rawOutput 2 G).1,
    (ClosureQueries.rawOutput 0 G).2,(ClosureQueries.rawOutput 1 G).2,(ClosureQueries.rawOutput 2 G).2)

 def rawQueryComputes (i : Fin 3) : Computes RawClosedNetwork.encoding RawClosedNetwork.encoding
    (fun G => (ClosureQueries.rawOutput i G).1) :=
  (ClosureQueries.rawComputes i).andThen (Wiring.firstComputes _ _)
 def rawFlagsComputes (i : Fin 3) : Computes RawClosedNetwork.encoding pairBoolEncoding
    (fun G => (ClosureQueries.rawOutput i G).2) :=
  (ClosureQueries.rawComputes i).andThen (Wiring.secondComputes _ _)
 def closuresComputes : Computes RawClosedNetwork.encoding rawPlanEncoding closures :=
  pairComputes (rawQueryComputes 0) (pairComputes (rawQueryComputes 1)
    (pairComputes (rawQueryComputes 2)
      (pairComputes (rawFlagsComputes 0) (pairComputes (rawFlagsComputes 1) (rawFlagsComputes 2)))))

 theorem closures_spec (L : Language) (g : Signature AlgebraicComplex 2)
    (G : TaggedInstance L g (fun k => k = 2)) : closures G.val.val = toRaw (ClosureQueries.pre L g G) := by
  have he (i : Fin 3) := RawClosures.eq_close G.val.property (tagged_arity_zero L g)
    (show 2 ≤ BellReduction.RawOccurrence.markedCount G.val.val.vertices from G.property.ge) i
  unfold closures ClosureQueries.rawOutput
  rw [he 0,he 1,he 2]
  rfl

 def witness (W : RawClosedNetwork) (G : RawClosedNetwork) : RawPlan :=
  closures (BellReduction.RawDisjointUnion.union G W)
 def witnessComputes (W : RawClosedNetwork) : Computes RawClosedNetwork.encoding rawPlanEncoding (witness W) :=
  (FixedUnion.computes W).andThen closuresComputes

end
end Paper2.FixedFieldOutput.ResidualRawPlans
