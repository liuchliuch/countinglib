import PlanarHom.FiniteReachableAlphabetMachines

/-!
# Restricting a specified polynomial-time computer to finite support

This wrapper reuses `PlanarHom.FiniteReachableAlphabetMachines` on an actual
timed computer and generalizes its Boolean-codec wrapper to arbitrary external
alphabets. It does not attach a false
finiteness instance to the source alphabet: its result has subtype alphabets and
the same control data. The external alphabets, code functions, transition count,
and polynomial are unchanged. The finite output alphabet is supplied by the
external codec; the source `FinTM2` already bundles finite input and control.
-/

noncomputable section

namespace Counting.Computation.FiniteSupport

open Turing
open PlanarHom.FiniteReachableAlphabetMachines

variable {α β Γ₀ Γ₁ : Type} [Fintype Γ₁]
    {ea : α → List Γ₀} {eb : β → List Γ₁} {f : α → β}

/-- Output-alphabet finiteness is obtained from the specified external alphabet
equivalence, independently of all scratch-stack alphabets. -/
@[instance_reducible] def outputFintype (h : TM2ComputableInPolyTime ea eb f) : Fintype (h.tm.Γ h.tm.k₁) :=
  Fintype.ofEquiv Γ₁ h.outputAlphabet.symm

set_option backward.isDefEq.respectTransparency false in
/-- Compile the actual computer by restricting every stack to program support.
Every run has exactly the source run's transition count. -/
def computer (h : TM2ComputableInPolyTime ea eb f) : TM2ComputableInPolyTime ea eb f := by
  letI := outputFintype h
  exact {
    tm := machine h.tm
    inputAlphabet := (inputEquiv h.tm).trans h.inputAlphabet
    outputAlphabet := (outputEquiv h.tm).trans h.outputAlphabet
    time := h.time
    outputsFun a := {
      steps := (h.outputsFun a).steps
      steps_le_m := (h.outputsFun a).steps_le_m
      evals_in_steps := by
        have hout := (outputs h.tm
          ((ea a).map h.inputAlphabet.symm) ((eb (f a)).map h.outputAlphabet.symm)
          (h.time.eval (ea a).length) (h.outputsFun a)).evals_in_steps
        have hi : ((inputEquiv h.tm).trans h.inputAlphabet).invFun =
            (inputEquiv h.tm).symm ∘ h.inputAlphabet.symm := rfl
        have ho : ((outputEquiv h.tm).trans h.outputAlphabet).invFun =
            (outputEquiv h.tm).symm ∘ h.outputAlphabet.symm := rfl
        rw [hi, ho]
        simpa only [List.map_map, outputs_steps] using hout } }

/-- All alphabets of the compiled computer have actual finite enumerations. -/
@[instance_reducible] def computerCertificate (h : TM2ComputableInPolyTime ea eb f) :
    ∀ k, Fintype ((computer h).tm.Γ k) := by
  letI := outputFintype h
  exact alphabetFintypeOfMachine h.tm

/-- The source polynomial is retained literally. -/
@[simp] theorem computer_time (h : TM2ComputableInPolyTime ea eb f) :
    (computer h).time = h.time := rfl

/-- The source transition count is retained literally on every encoded input. -/
@[simp] theorem computer_steps (h : TM2ComputableInPolyTime ea eb f) (a : α) :
    ((computer h).outputsFun a).steps = (h.outputsFun a).steps := rfl

/-- Erasure from the compiled computer to the specified source computer. -/
def eraseComputerCfg (h : TM2ComputableInPolyTime ea eb f) :
    (computer h).tm.Cfg → h.tm.Cfg := by
  letI := outputFintype h
  exact eraseCfg (allowedSymbols h.tm)

/-- The computer compiler preserves every actual transition, including halt. -/
theorem computer_erase_step (h : TM2ComputableInPolyTime ea eb f)
    (c : (computer h).tm.Cfg) :
    Option.map (eraseComputerCfg h) ((computer h).tm.step c) =
      h.tm.step (eraseComputerCfg h c) := by
  let := outputFintype h
  exact erase_step h.tm c

end Counting.Computation.FiniteSupport
