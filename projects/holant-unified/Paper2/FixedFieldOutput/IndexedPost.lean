import Paper2.FixedFieldOutput.BellPostprocessing
import Paper2.Complexity.BellMachines.ListCombinators

/-! Three-query postprocessing selected by the physically retained occurrence
count (0,1,2). Each finite branch is a fixed rational-coordinate program. -/
namespace Paper2.FixedFieldOutput.IndexedPost
open Computability Paper2.Complexity BinaryCompose FixedFieldMachines BellMachines
open GraphPreprocessing UniversalPairReduction.ThreeQuery Paper2.ExactInput
open BellPostprocessing
noncomputable section

abbrev indexEncoding := Codecs.unaryPortEncoding 3
abbrev context := pairEncoding flagsEncoding indexEncoding
abbrev Input (L : Language) := Answer L × (Answer L × (Answer L × (Flags × Fin 3)))
abbrev encoding (L : Language) := contextEncoding (answerEncoding L) context

 def strip (L : Language) (p : Input L) : PostInput L := (p.1,p.2.1,p.2.2.1,p.2.2.2.1)
 def index (L : Language) (p : Input L) : Fin 3 := p.2.2.2.2

 def stripComputes (L : Language) : Computes (encoding L) (postEncoding L) (strip L) := by
  let a := Wiring.firstComputes (answerEncoding L)
    (pairEncoding (answerEncoding L) (pairEncoding (answerEncoding L) context))
  let tail := Wiring.secondComputes (answerEncoding L)
    (pairEncoding (answerEncoding L) (pairEncoding (answerEncoding L) context))
  let b := tail.andThen (Wiring.firstComputes (answerEncoding L) (pairEncoding (answerEncoding L) context))
  let tail2 := tail.andThen (Wiring.secondComputes (answerEncoding L) (pairEncoding (answerEncoding L) context))
  let c := tail2.andThen (Wiring.firstComputes (answerEncoding L) context)
  let flags := (tail2.andThen (Wiring.secondComputes (answerEncoding L) context)).andThen
    (Wiring.firstComputes flagsEncoding indexEncoding)
  exact pairComputes a (pairComputes b (pairComputes c flags))

 def indexComputes (L : Language) : Computes (encoding L) indexEncoding (index L) :=
  (((Wiring.secondComputes _ _).andThen (Wiring.secondComputes _ _)).andThen
    (Wiring.secondComputes _ _)).andThen (Wiring.secondComputes _ _)

 def post (base work : Language) (coeff : Fin 3 → Fin 3 → work.coefficientField) (p : Input base) : Answer work :=
  BellPostprocessing.post base work (coeff (index base p)) (strip base p)

 def computes (base work : Language) (coeff : Fin 3 → Fin 3 → work.coefficientField) :
    Computes (encoding base) (answerEncoding work) (post base work coeff) :=
  Lists.chooseComputes (encoding base) (answerEncoding work) 3 (index base)
    (fun p i => BellPostprocessing.post base work (coeff i) (strip base p))
    (recode (indexComputes base) id (fun _ => rfl) (fun _ => rfl))
    (fun i => (stripComputes base).andThen (BellPostprocessing.computes base work (coeff i)))

end
end Paper2.FixedFieldOutput.IndexedPost
