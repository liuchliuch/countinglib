import Paper2.ExactInput.Recognition.PromisedReturningLoop
import Paper2.ExactInput.Recognition.NativeCandidateSelection
import Holant.Proofs.AlgebraicRecognition.WitnessOutput.ReturnedRootBranchSelection.Bounded

/-! One actual search controller for certified varying-layout table conversion.
Every finite stage is executed on the proved source domain. Completeness
provides a least successful height only in the termination proof. -/
namespace Paper2.ExactInput.Recognition.NativeSearchController
open Turing Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.RemoteWork.TractChainV1.PhysicalFolds
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open CommonFieldMachine (Executes)
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {D A B : Type} (ea : Encoding A Bool) (eb : Encoding B Bool)
variable (context : D → A) (stage : D × ℕ → Option B)
variable (stages : Runs (pairEncoding ea encodingNatBool)
  (Holant.OneHot.StackProgram.GraphLabelEncoding.optionEncoding eb)
  (fun d : D × ℕ => (context d.1,d.2)) stage)

abbrev resultEncoding := Holant.OneHot.StackProgram.GraphLabelEncoding.optionEncoding eb
abbrev requestEncoding := pairEncoding ea encodingNatBool
abbrev stateEncoding := pairEncoding (requestEncoding ea) (resultEncoding eb)
abbrev State (D B : Type) := D × (ℕ × Option B)
def input (d : State D B) : (A × ℕ) × Option B := ((context d.1,d.2.1),d.2.2)
def next (d : State D B) : State D B := (d.1,d.2.1+1,stage (d.1,d.2.1))
def keep (d : State D B) : Bool := (stage (d.1,d.2.1)).isNone

def bumpComputes : Computes (stateEncoding ea eb) (requestEncoding ea)
    (fun s : (A × ℕ) × Option B => (s.1.1,s.1.2+1)) := by
  let req := Wiring.firstComputes (requestEncoding ea) (resultEncoding eb)
  let ctx := req.andThen (Wiring.firstComputes ea encodingNatBool)
  let h := req.andThen (Wiring.secondComputes ea encodingNatBool)
  exact pairComputes ctx (h.andThen RationalInputMachine.Programs.successor)

def finishComputes : Computes (pairEncoding (resultEncoding eb) (requestEncoding ea))
    (pairEncoding encodingBoolBool (stateEncoding ea eb))
    (fun s : Option B × (A × ℕ) => (s.1.isNone,(s.2,s.1))) := by
  let opt := Wiring.firstComputes (resultEncoding eb) (requestEncoding ea)
  let req := Wiring.secondComputes (resultEncoding eb) (requestEncoding ea)
  let some := opt.andThen (NativeCandidateSelection.presence eb)
  let flag := some.andThen (Holant.LocalDrafts.Tractability.ProductMachine.Rewrite.negComputes)
  exact congrComputes (pairComputes flag (pairComputes req opt))
    (fun s => by rcases s with ⟨o,r⟩; cases o <;> rfl)

def stageRuns : Runs (stateEncoding ea eb) (resultEncoding eb)
    (input context) (fun d => stage (d.1,d.2.1)) := by
  let projected : Runs (stateEncoding ea eb) (requestEncoding ea)
      (input context) (fun d => (context d.1,d.2.1)) :=
    Runs.ofComputes (Wiring.firstComputes (requestEncoding ea) (resultEncoding eb)) (input context)
  let repeated : Runs (requestEncoding ea) (resultEncoding eb)
      (fun d : State D B => (context d.1,d.2.1)) (fun d => stage (d.1,d.2.1)) :=
    ⟨stages.machine,fun d => stages.cost (d.1,d.2.1),fun d => stages.outputs (d.1,d.2.1)⟩
  exact projected.comp repeated

def body : Runs (stateEncoding ea eb) (pairEncoding encodingBoolBool (stateEncoding ea eb))
    (input context) (fun d => (keep stage d,input context (next stage d))) :=
  ((stageRuns ea eb context stage stages).pair
    (Runs.ofComputes (bumpComputes ea eb) (input context))).after (finishComputes ea eb)

theorem disjoint : (body ea eb context stage stages).machine.output ≠
    (body ea eb context stage stages).machine.input := by
  intro h
  cases h

abbrev loop := PromisedReturningLoop.machine (input context) (next stage) (keep stage)
  (body ea eb context stage stages)

variable (termination : ∀ d, ∃ h, (stage (d,h)).isSome=true)

def height (d : D) : ℕ := Nat.find (termination d)
def result (d : D) : Option B := stage (d,height stage termination d)

theorem result_some (d : D) : (result stage termination d).isSome=true := Nat.find_spec (termination d)

theorem next_source (d : D) (h : ℕ) (old : Option B) (n : ℕ) :
    ((next stage)^[n] (d,h,old)).1=d ∧
      ((next stage)^[n] (d,h,old)).2.1=h+n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simp only [next,ih.1,ih.2]
    exact ⟨True.intro,by omega⟩

theorem next_old (d : D) (h : ℕ) (old : Option B) (n : ℕ) :
    ((next stage)^[n+1] (d,h,old)).2.2=stage (d,h+n) := by
  rw [Function.iterate_succ_apply']
  have hs := next_source stage d h old n
  simp only [next,hs.1,hs.2]

/-- The initial stage starts at zero, with no supplied candidate or stop index. -/
def prepare : Computes ea (stateEncoding ea eb) (fun a : A => ((a,0),none)) :=
  pairComputes (pairComputes (identityComputes ea) (constantComputes ea encodingNatBool 0))
    (constantComputes ea (resultEncoding eb) none)

def extract : Computes (stateEncoding ea eb) (resultEncoding eb) Prod.snd :=
  Wiring.secondComputes (requestEncoding ea) (resultEncoding eb)

abbrev machine := ((prepare ea eb).machine.compose (loop ea eb context stage stages)).compose
  (extract ea eb).machine

theorem outputs (d : D) :
    ∃ ticks, Nonempty (TM2OutputsInTime (machine ea eb context stage stages).computer
      (ea.encode (context d))
      (some ((resultEncoding eb).encode (result stage termination d))) ticks) := by
  let n := height stage termination d
  have before : ∀ j < n, keep stage ((next stage)^[j] (d,0,none))=true := by
    intro j hj
    have hn : ¬ (stage (d,j)).isSome=true := Nat.find_min (termination d) hj
    have hs := next_source stage d 0 none j
    simp only [keep,hs.1,hs.2,Nat.zero_add]
    cases he : stage (d,j) with
    | none => rfl
    | some b => simp [he] at hn
  have last : keep stage ((next stage)^[n] (d,0,none))=false := by
    have hs := next_source stage d 0 none n
    have hn := Nat.find_spec (termination d)
    simp only [keep,hs.1,hs.2,Nat.zero_add]
    change (stage (d,n)).isSome=true at hn
    cases he : stage (d,n) with
    | none => simp [he] at hn
    | some b => rfl
  obtain ⟨t,⟨hr⟩⟩ := PromisedReturningLoop.outputs_of_first (input context) (next stage)
    (keep stage) (body ea eb context stage stages) (disjoint ea eb context stage stages)
    n (d,0,none) before last
  have first := Machine.compose_correct _ _ _ _ _ _ _ ((prepare ea eb).outputs (context d)) hr
  have full := Machine.compose_correct _ _ _ _ _ _ _ first
    ((extract ea eb).outputs (input context ((next stage)^[n+1] (d,0,none))))
  have he : (input context ((next stage)^[n+1] (d,0,none))).2=result stage termination d := by
    change ((next stage)^[n+1] (d,0,none)).2.2=stage (d,n)
    simpa only [Nat.zero_add] using next_old stage d 0 none n
  rw [he] at full
  exact ⟨_,⟨full⟩⟩

/-- The cost is derived from the actual finite run, without a polynomial claim.
Its value is a proof index; it is absent from the machine and input bytes. -/
def runs : Runs ea (resultEncoding eb) context (result stage termination) where
  machine := machine ea eb context stage stages
  cost d := Classical.choose (outputs ea eb context stage stages termination d)
  outputs d := Classical.choice (Classical.choose_spec (outputs ea eb context stage stages termination d))

end
end Paper2.ExactInput.Recognition.NativeSearchController
