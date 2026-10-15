import Paper2.FixedFieldOutput.LinearMachines
import Paper2.Complexity.ControlledCompose
import Paper2.Complexity.BellMachines.ThreeQuerySafe

/-! Canonical field-output reduction closure and machine-level transport of
actual value-preserving graph maps. No representation conversion is inferred
from a size bound: fixed rational linear converters are executed explicitly. -/
namespace Paper2.FixedFieldOutput
open Computability Paper2.Complexity BinaryCompose FixedFieldMachines
open Paper2.ExactInput Paper2.Problem
open UniversalPairReduction.ThreeQuery
noncomputable section

 theorem Reduces.trans {w : Wiring} {A B C : Language}
    (hAB : Reduces w A B) (hBC : Reduces w B C) : Reduces w A C := by
  obtain ⟨rAB⟩ := hAB
  obtain ⟨rBC⟩ := hBC
  exact ⟨rAB.controlledCompose rBC⟩

 theorem SharpPHard.transport {w : Wiring} {source target : Language}
    (hard : SharpPHard w source) (r : Reduces w source target) : SharpPHard w target := by
  obtain ⟨r⟩ := r
  intro f hf
  obtain ⟨counting⟩ := hard f hf
  exact ⟨counting.controlledCompose r⟩

/-- A real constant-query adapter. The same valid graph query is made three
 times by the already checked general controller; unused answers are erased. -/
def sameValueReduction (ws wt : Wiring) (source target : Language)
    (q : Instance source → Instance target)
    (pre : Computes (inputEncoding source) (inputEncoding target) q)
    (h : ∀ G, value ws source G = value wt target (q G)) :
    LengthControlledOracleReduction (inputEncoding source) (answerEncoding source)
      (inputEncoding target) (answerEncoding target) (answer ws source) (answer wt target) := by
  let pre3 := pairComputes pre (pairComputes pre
    (pairComputes pre (constantComputes (inputEncoding source) encodingBoolBool false)))
  let first := Wiring.firstComputes (answerEncoding target)
    (pairEncoding (answerEncoding target) (pairEncoding (answerEncoding target) encodingBoolBool))
  let post := first.andThen (conversionComputes target source)
  exact controlledOfEq pre3 post (outputBound wt target) (answer ws source)
    (fun G => (conversion_answer wt ws target source (q G) G (h G).symm).symm)

 theorem booleanFP_of_sameValue (ws wt : Wiring) (source target : Language)
    (q : Instance source → Instance target)
    (pre : Computes (inputEncoding source) (inputEncoding target) q)
    (h : ∀ G, value ws source G = value wt target (q G))
    (ht : BooleanFP wt target) : BooleanFP ws source := by
  obtain ⟨eval⟩ := ht
  exact ⟨congrComputes ((pre.andThen eval).andThen (conversionComputes target source))
    (fun G => conversion_answer wt ws target source (q G) G (h G).symm)⟩

 theorem hard_of_sameValue (ws wt : Wiring) (source target : Language)
    (q : Instance source → Instance target)
    (pre : Computes (inputEncoding source) (inputEncoding target) q)
    (h : ∀ G, value ws source G = value wt target (q G))
    (hs : SharpPHard ws source) : SharpPHard wt target := by
  intro f hf
  obtain ⟨r⟩ := hs f hf
  exact ⟨r.controlledCompose (sameValueReduction ws wt source target q pre h)⟩

/-- This is the identity word machine with a different validated input type. -/
def sameBytesComputes (source target : Language) (q : Instance source → Instance target)
    (bytes : ∀ G, (inputEncoding target).encode (q G) = (inputEncoding source).encode G) :
    Computes (inputEncoding source) (inputEncoding target) q :=
  recode (identityComputes (inputEncoding source)) id (fun _ => rfl) (fun G => (bytes G).symm)

end
end Paper2.FixedFieldOutput
