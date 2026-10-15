import ComplexCSP.Structure.MaltsevTypeMaterialized

/-!
# Explicit continuation machine for materialized prefix-type search

This module owns the shared transition definition. Reconstruction and row-label
callbacks are mathematical arguments here; the separate machine compiler
instantiates them by actual FP computations on immutable ordinary input data.
No function closure is a serialized state field.
-/
namespace ComplexCSP.MaltsevTypeStack
open MaltsevWitness
variable {A : Type*} [DecidableEq A]

structure Frame (A : Type*) where
  parentLen : ℕ
  parentTarget : List ℕ
  remainingColors : List ℕ
  accumulatedLabels : List A
  deriving DecidableEq

structure State (A : Type*) where
  returning : Bool
  currentLen : ℕ
  currentTarget : List ℕ
  returnedLabels : List A
  stack : List (Frame A)
  cache : ListTypeCache A
  deriving DecidableEq

def replaceAt (target : List ℕ) (i a : ℕ) : List ℕ :=
  target.zipIdx.map (fun p => if p.2 = i then a else p.1)

@[simp] theorem replaceAt_length (target : List ℕ) (i a : ℕ) :
    (replaceAt target i a).length = target.length := by simp [replaceAt]

def callState (len : ℕ) (target : List ℕ) (stack : List (Frame A))
    (cache : ListTypeCache A) : State A :=
  ⟨false, len, target, [], stack, cache⟩

def returnState (len : ℕ) (target : List ℕ) (labels : List A)
    (stack : List (Frame A)) (cache : ListTypeCache A) : State A :=
  ⟨true, len, target, labels, stack, cache⟩

/-- One literal control transition. Lengths use unary codecs in the machine
implementation; colors are the fixed finite domain list. None is the final halt. -/
def step (dimension : ℕ) (colors : List ℕ)
    (reconstruct : ℕ → List ℕ → Option (List ℕ)) (label : List ℕ → A)
    (state : State A) : Option (State A) :=
  if state.returning then
    match state.stack with
    | [] => none
    | frame :: rest =>
      let combined := (frame.accumulatedLabels ++ state.returnedLabels).dedup
      match frame.remainingColors with
      | [] => some (returnState frame.parentLen frame.parentTarget combined rest
          ((frame.parentLen, combined) :: state.cache))
      | a :: colorsLeft =>
        let frame' : Frame A := ⟨frame.parentLen, frame.parentTarget, colorsLeft, combined⟩
        some (callState (frame.parentLen + 1) (replaceAt frame.parentTarget frame.parentLen a)
          (frame' :: rest) state.cache)
  else
    match reconstruct state.currentLen state.currentTarget with
    | none => some (returnState state.currentLen state.currentTarget [] state.stack state.cache)
    | some witness =>
      let a := label witness
      match cachedTypeList state.cache state.currentLen a with
      | some labels => some (returnState state.currentLen state.currentTarget labels.dedup state.stack state.cache)
      | none =>
        if state.currentLen < dimension then
          match colors with
          | [] => some (returnState state.currentLen state.currentTarget [] state.stack
              ((state.currentLen, []) :: state.cache))
          | b :: rest =>
            let frame : Frame A := ⟨state.currentLen, state.currentTarget, rest, []⟩
            some (callState (state.currentLen + 1) (replaceAt state.currentTarget state.currentLen b)
              (frame :: state.stack) state.cache)
        else some (returnState state.currentLen state.currentTarget [a] state.stack
          ((state.currentLen, [a]) :: state.cache))

/-- Exactly t successful transitions, without assuming an abstract execution oracle. -/
inductive Runs (transition : State A → Option (State A)) : State A → State A → ℕ → Prop
  | refl (s) : Runs transition s s 0
  | step {s u t k} : transition s = some u → Runs transition u t k → Runs transition s t (k + 1)

theorem Runs.trans {transition : State A → Option (State A)} {s u t : State A} {k l : ℕ}
    (h : Runs transition s u k) (h' : Runs transition u t l) : Runs transition s t (k + l) := by
  induction h with
  | refl => simpa using h'
  | step he hs ih => simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Runs.step he (ih h')

end ComplexCSP.MaltsevTypeStack
