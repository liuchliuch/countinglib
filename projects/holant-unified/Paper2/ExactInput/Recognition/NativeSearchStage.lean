import Paper2.ExactInput.Recognition.NativeCandidateSelection
import Holant.Proofs.Recognition.PromisedListMap

/-! A finite runtime candidate stage with a proved per-member domain. All
actual candidates are checked by the same cell machine; the first true cell is
selected from the returned Boolean bytes. -/
namespace Paper2.ExactInput.Recognition.NativeSearchStage
open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.RemoteWork.TractChainV1
open PhysicalFolds
noncomputable section

variable {D A B : Type} (ea : Encoding A Bool) (eb : Encoding B Bool)
variable (context : D → A) (items : D → List B) (test : D → B → Bool)
variable (itemsRuns : Runs ea (framedListEncoding eb) context items)
variable (cells : Runs (pairEncoding ea eb) encodingBoolBool
  (PromisedListMap.cellInput context items) (fun d => test d.1 d.2.val))

def packets (d : D) : List (Bool × B) := (items d).map (fun b => (test d b,b))
def stage (d : D) : Option B := NativeCandidateSelection.select (packets items test d)

def flagged : Runs (pairEncoding ea eb) (pairEncoding encodingBoolBool eb)
    (PromisedListMap.cellInput context items) (fun d => (test d.1 d.2.val,d.2.val)) :=
  cells.pair (Runs.ofComputes (Wiring.secondComputes ea eb) (PromisedListMap.cellInput context items))

def runs : Runs ea (Holant.OneHot.StackProgram.GraphLabelEncoding.optionEncoding eb) context (stage items test) :=
  ((Runs.ofComputes (identityComputes ea) context).pair itemsRuns).comp
    ((PromisedListMap.mapList (flagged ea eb context items test cells)).after
      (NativeCandidateSelection.selectComputes eb))

theorem isSome_iff (d : D) : (stage items test d).isSome=true ↔
    ∃ b ∈ items d, test d b=true := by
  rw [stage,NativeCandidateSelection.isSome_iff]
  constructor
  · rintro ⟨b,hb⟩
    obtain ⟨a,ha,he⟩ := List.mem_map.mp hb
    have hab : a=b := congrArg Prod.snd he
    subst a
    exact ⟨b,ha,congrArg Prod.fst he⟩
  · rintro ⟨b,hb,ht⟩
    exact ⟨b,List.mem_map.mpr ⟨b,hb,by simp only [ht]⟩⟩

theorem some_mem {d : D} {b : B} (h : stage items test d=some b) :
    b ∈ items d ∧ test d b=true := by
  have hb := NativeCandidateSelection.some_mem h
  obtain ⟨a,ha,he⟩ := List.mem_map.mp hb
  have hab : a=b := congrArg Prod.snd he
  subst a
  exact ⟨ha,congrArg Prod.fst he⟩

end
end Paper2.ExactInput.Recognition.NativeSearchStage
