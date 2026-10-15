import Holant.Proofs.Tractability.AffineMachine.AccessPrograms
import Holant.Proofs.Algorithms.OptionalValue
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionMapInterface
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.OptionAny

/-! Physical selection of the first successful runtime candidate.
The Boolean checks are explicit list entries, and all operations are total.
No algebraic validity or successful-candidate promise is used here. -/
namespace Paper2.ExactInput.Recognition.NativeCandidateSelection
open Computability Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open UniversalPairReduction.SmoothingCompiler FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.Tractability.AffineMachine
open Holant.OneHot.StackProgram.GraphLabelEncoding

variable {B : Type}

def select (ps : List (Bool × B)) : Option B :=
  (ps.filter Prod.fst).head?.map Prod.snd

@[simp] theorem select_nil : select ([] : List (Bool × B)) = none := rfl

theorem select_cons (p : Bool × B) (ps : List (Bool × B)) :
    select (p::ps) = if p.1 then some p.2 else select ps := by
  rcases p with ⟨flag,b⟩
  cases flag <;> simp [select]

theorem isSome_iff (ps : List (Bool × B)) :
    (select ps).isSome = true ↔ ∃ b, (true,b) ∈ ps := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    rcases p with ⟨flag,b⟩
    cases flag <;> simp [select_cons,ih]

theorem some_mem {ps : List (Bool × B)} {b : B} (h : select ps = some b) :
    (true,b) ∈ ps := by
  induction ps with
  | nil => simp at h
  | cons p ps ih =>
    rcases p with ⟨flag,a⟩
    cases flag with
    | false =>
      have hs : select ps = some b := by simpa [select_cons] using h
      exact List.mem_cons_of_mem _ (ih hs)
    | true =>
      have hab : a=b := by simpa [select_cons] using h
      subst a
      exact List.mem_cons_self

theorem select_append_of_false (before after : List (Bool × B))
    (hb : ∀ p ∈ before, p.1 = false) : select (before++after) = select after := by
  induction before with
  | nil => rfl
  | cons p before ih =>
    have hp := hb p (List.mem_cons_self ..)
    rw [List.cons_append,select_cons,hp]
    exact ih (fun q hq => hb q (List.mem_cons_of_mem _ hq))

theorem first_true_iff (ps : List (Bool × B)) (b : B) :
    select ps = some b ↔
      ∃ before after : List (Bool × B),
        ps = before ++ (true,b)::after ∧ ∀ p ∈ before, p.1 = false := by
  constructor
  · intro h
    induction ps with
    | nil => simp at h
    | cons p ps ih =>
      rcases p with ⟨flag,a⟩
      cases flag with
      | true =>
        have hab : a=b := by simpa [select_cons] using h
        subst a
        exact ⟨[],ps,rfl,by simp⟩
      | false =>
        have hs : select ps=some b := by simpa [select_cons] using h
        obtain ⟨before,after,he,hb⟩ := ih hs
        refine ⟨(false,a)::before,after,by simp only [List.cons_append,he],?_⟩
        intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · rfl
        · exact hb p hp
  · rintro ⟨before,after,rfl,hb⟩
    rw [select_append_of_false before _ hb,select_cons]
    rfl

noncomputable section
variable (eb : Encoding B Bool)

abbrev pairEncodingB := pairEncoding encodingBoolBool eb
abbrev inputEncoding := framedListEncoding (pairEncodingB eb)
abbrev resultEncoding := optionEncoding eb

def someComputes : Computes eb (resultEncoding eb) (fun b => some b) :=
  recode (joinComputes (constantComputes eb Frame.wordEncoding [true])
    (encodeComputes eb)) id (fun _ => rfl) (fun _ => rfl)

def headComputes : Computes (framedListEncoding eb) (resultEncoding eb) List.head? :=
  congrComputes
    ((WireLists.mapComputes eb (resultEncoding eb) (fun b => some b) (someComputes eb)).andThen
      (getDComputes (resultEncoding eb) 0 none))
    (fun bs => by cases bs <;> rfl)

def acceptedComputes : Computes (pairEncodingB eb) (framedListEncoding eb)
    (fun p : Bool × B => if p.1 then [p.2] else []) :=
  ifComputes (Wiring.firstComputes encodingBoolBool eb)
    (fixedListComputes (pairEncodingB eb) eb (fun p (_ : Unit) => p.2)
      (fun _ => Wiring.secondComputes encodingBoolBool eb) [()])
    (constantComputes (pairEncodingB eb) (framedListEncoding eb) [])

def acceptedListComputes : Computes (inputEncoding eb) (framedListEncoding eb)
    (fun ps : List (Bool × B) => (ps.filter Prod.fst).map Prod.snd) :=
  congrComputes
    (AccessPrograms.flatMap (pairEncodingB eb) eb
      (fun p : Bool × B => if p.1 then [p.2] else []) (acceptedComputes eb))
    (fun ps => by
      induction ps with
      | nil => rfl
      | cons p ps ih =>
        rcases p with ⟨flag,b⟩
        cases flag <;> simp [ih])

/-- One actual total program, with the checked Booleans supplied literally. -/
def selectComputes : Computes (inputEncoding eb) (resultEncoding eb) select :=
  congrComputes ((acceptedListComputes eb).andThen (headComputes eb))
    (fun ps => by simp only [Function.comp_apply,select,List.head?_map])

def presence : Computes (resultEncoding eb) encodingBoolBool Option.isSome :=
  congrComputes
    ((OriginalCoefficient.OptionMap.computes
      (constantComputes eb encodingBoolBool true)).andThen OriginalCoefficient.OptionAny.computes)
    (fun q => by cases q <;> rfl)

def getDComputes (fallback : B) :
    Computes (resultEncoding eb) eb (fun q => q.getD fallback) :=
  Holant.LocalDrafts.MainChain.OptionalValue.getDComputes eb fallback

end
end Paper2.ExactInput.Recognition.NativeCandidateSelection
