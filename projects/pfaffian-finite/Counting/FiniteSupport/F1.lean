import Counting.FiniteSupport
import Counting.Computation.PolyTime

/-! # The finite-support compiler in the shared F1 interface -/

noncomputable section

namespace Counting.Computation.FiniteSupport

variable {α β Γ₀ Γ₁ : Type} [Fintype Γ₀] [Fintype Γ₁]
    {ea : Computability.Encoding α Γ₀} {eb : Computability.Encoding β Γ₁}
    {f : α → β}

/-- Compile a specified raw witness and package its proved finite alphabets in F1.
Faithful external encodings are retained as the same parameters. -/
def toPolyTime (h : Turing.TM2ComputableInPolyTime ea.encode eb.encode f) :
    Counting.Computation.PolyTime ea eb f where
  toTM2ComputableInPolyTime := computer h
  finiteAlphabets := computerCertificate h

@[simp] theorem toPolyTime_time (h : Turing.TM2ComputableInPolyTime ea.encode eb.encode f) :
    (toPolyTime h).time = h.time := rfl

@[simp] theorem toPolyTime_steps (h : Turing.TM2ComputableInPolyTime ea.encode eb.encode f)
    (a : α) : ((toPolyTime h).outputsFun a).steps = (h.outputsFun a).steps := rfl

/-- The existential corollary uses the real finite-support compiler for the given
source witness; it never infers finiteness of the original scratch alphabets. -/
theorem inFP (h : Nonempty (Turing.TM2ComputableInPolyTime ea.encode eb.encode f)) :
    Counting.Computation.InFP ea eb f := by
  obtain ⟨h⟩ := h
  exact ⟨toPolyTime h⟩

end Counting.Computation.FiniteSupport
