import PfaffianPort.MachineComposition
import PfaffianPort.MachineOutputTransport
import PfaffianPort.OracleSubstitution
import PfaffianPort.MachinePairing

/-!
# An explicit finite-stack-alphabet refinement boundary

This module keeps the migrated `PfaffianPort.Complexity.FP` definition unchanged.
`FiniteComputer` records exactly the additional all-stack finiteness data required
by F1's `Counting.Computation.PolyTime`. No theorem here asserts that the migrated
Pfaffian evaluator has already been supplied with that additional data.

The examples below distinguish a property of one particular machine witness from
an extensional claim about its computed function. The identity function has a
finite-alphabet implementation even though `extraStackIdentity` has an unused
infinite alphabet. Thus the example does not separate two complexity classes.
-/

namespace Counting.Algorithm.Pfaffian

open Turing

/-- Finiteness of every alphabet of a specified machine, including scratch stacks. -/
abbrev StackAlphabetCertificate (tm : FinTM2) := ∀ k, Fintype (tm.Γ k)

/-- A timed TM2 witness together with its all-stack alphabet certificate.
The code functions are explicit parameters; faithful codecs are supplied by clients. -/
structure FiniteComputer {α β Γ₀ Γ₁ : Type}
    (ea : α → List Γ₀) (eb : β → List Γ₁) (f : α → β)
    extends TM2ComputableInPolyTime ea eb f where
  finiteAlphabets : StackAlphabetCertificate tm

namespace FiniteComputer

variable {α β γ Γ₀ Γ₁ Γ₂ : Type} {ea : α → List Γ₀}
    {eb : β → List Γ₁} {ec : γ → List Γ₂} {f : α → β} {g : β → γ}

/-- Forgetting the certificate retains the identical machine and timed execution. -/
theorem forget_nonempty (h : Nonempty (FiniteComputer ea eb f)) :
    Nonempty (TM2ComputableInPolyTime ea eb f) := by
  obtain ⟨h⟩ := h
  exact ⟨h.toTM2ComputableInPolyTime⟩

/-- A proved instance, using the actual one-step identity machine. -/
noncomputable def identity [Fintype Γ₀] (e : α → List Γ₀) :
    FiniteComputer e e id := by
  refine ⟨idComputableInPolyTime e, ?_⟩
  intro k
  exact inferInstanceAs (Fintype Γ₀)

/-- Compile two certified machines without changing the source compiler or its
polynomial. Each stack of the result comes from one of the two certified banks. -/
noncomputable def comp (hf : FiniteComputer ea eb f) (hg : FiniteComputer eb ec g) :
    FiniteComputer ea ec (g ∘ f) := by
  letI := hf.finiteAlphabets
  letI := hg.finiteAlphabets
  exact {
    toTM2ComputableInPolyTime := PfaffianPort.MachineComposition.composeComputers
      hf.toTM2ComputableInPolyTime hg.toTM2ComputableInPolyTime
    finiteAlphabets := PfaffianPort.MachineComposition.sequentialAlphabetFintype hf.tm hg.tm
      (hf.outputAlphabet.trans hg.inputAlphabet.symm) }

/-- Refinement does not change the compiler's actual execution count. -/
@[simp] theorem comp_steps (hf : FiniteComputer ea eb f) (hg : FiniteComputer eb ec g)
    (a : α) : ((comp hf hg).outputsFun a).steps =
      (hg.outputsFun (f a)).steps + (hf.outputsFun a).steps := rfl

/-- Refinement retains the proved output-length charge for the intermediate word. -/
@[simp] theorem comp_time (hf : FiniteComputer ea eb f) (hg : FiniteComputer eb ec g) :
    (comp hf hg).time = hg.time.comp
      (PfaffianPort.MachineComposition.outputLengthPolynomial hf.toTM2ComputableInPolyTime)
        + hf.time := rfl

/-- A certified Boolean computer supplies the unchanged upstream FP proposition. -/
theorem toUpstreamFP {A B : Type} {a : PfaffianPort.Complexity.BitEncoding A}
    {b : PfaffianPort.Complexity.BitEncoding B} {F : A → B}
    (h : FiniteComputer a.encode b.encode F) : PfaffianPort.Complexity.FP a b F :=
  ⟨h.toTM2ComputableInPolyTime⟩

/-- The two input banks and the Boolean transfer stack are all the alphabets
introduced by the literal pairing machine. -/
@[instance_reducible] def pairingCertificate (a b : TM2ComputableAux Bool Bool)
    (ha : StackAlphabetCertificate a.tm) (hb : StackAlphabetCertificate b.tm) :
    StackAlphabetCertificate (PfaffianPort.MachinePairing.machine a b)
  | .inl k => ha k
  | .inr (.inl k) => hb k
  | .inr (.inr _) => inferInstanceAs (Fintype Bool)

/-- Preserve the input and compute two outputs with the original pairing compiler. -/
noncomputable def pair {A B C : Type} {a : PfaffianPort.Complexity.BitEncoding A}
    {b : PfaffianPort.Complexity.BitEncoding B} {c : PfaffianPort.Complexity.BitEncoding C}
    {F : A → B} {G : A → C} (hf : FiniteComputer a.encode b.encode F)
    (hg : FiniteComputer a.encode c.encode G) :
    FiniteComputer a.encode (b.prod c).encode (fun x => (F x, G x)) := by
  exact ⟨PfaffianPort.MachinePairing.pairComputers hf.toTM2ComputableInPolyTime
    hg.toTM2ComputableInPolyTime, pairingCertificate hf.toTM2ComputableAux
      hg.toTM2ComputableAux hf.finiteAlphabets hg.finiteAlphabets⟩

/-- The actual framed-prefix parser has Boolean input and scratch stacks. -/
noncomputable def fst {A B : Type} (a : PfaffianPort.Complexity.BitEncoding A)
    (b : PfaffianPort.Complexity.BitEncoding B) :
    FiniteComputer (a.prod b).encode a.encode Prod.fst := by
  refine ⟨PfaffianPort.Complexity.PairProjectionMachines.fstEncodingComputer a b, ?_⟩
  intro k
  exact inferInstanceAs (Fintype Bool)

/-- The actual framed-suffix parser also has Boolean input and scratch stacks. -/
noncomputable def snd {A B : Type} (a : PfaffianPort.Complexity.BitEncoding A)
    (b : PfaffianPort.Complexity.BitEncoding B) :
    FiniteComputer (a.prod b).encode b.encode Prod.snd := by
  refine ⟨PfaffianPort.Complexity.PairProjectionMachines.sndEncodingComputer a b, ?_⟩
  intro k
  exact inferInstanceAs (Fintype Bool)

/-- Literal input-code transport retains the same machine and its certificate. -/
noncomputable def transportInput {A B C : Type}
    (a : PfaffianPort.Complexity.BitEncoding A) (b : PfaffianPort.Complexity.BitEncoding B)
    (c : PfaffianPort.Complexity.BitEncoding C) (view : A → B)
    (sameWords : ∀ x, b.encode (view x) = a.encode x) {F : B → C}
    (h : FiniteComputer b.encode c.encode F) : FiniteComputer a.encode c.encode (F ∘ view) := by
  exact ⟨PfaffianPort.Complexity.transportInputComputer a b c view sameWords
    h.toTM2ComputableInPolyTime, h.finiteAlphabets⟩

/-- Literal output-code transport also keeps the certified machine unchanged. -/
noncomputable def transportOutput {A B C : Type}
    (a : PfaffianPort.Complexity.BitEncoding A) (b : PfaffianPort.Complexity.BitEncoding B)
    (c : PfaffianPort.Complexity.BitEncoding C) {F : A → B} {G : A → C}
    (sameWords : ∀ x, b.encode (F x) = c.encode (G x))
    (h : FiniteComputer a.encode b.encode F) : FiniteComputer a.encode c.encode G := by
  exact ⟨PfaffianPort.Complexity.transportOutputComputer a b c sameWords
    h.toTM2ComputableInPolyTime, h.finiteAlphabets⟩

/-- A query-free oracle program is already a certified ordinary computer. -/
noncomputable def ofNoQueries {target oracle : List Bool → List Bool}
    (r : PfaffianPort.Complexity.PolyTimeTuringReduction target oracle)
    (h : ∀ l, r.machine.request l = none) : FiniteComputer id id target := by
  exact ⟨r.toComputerOfNoQueries h, r.machine.finiteAlphabet⟩

/-- Substituting a certified callee into a concrete oracle reduction retains all
stack certificates and the existing exact-run and charged-time proof. -/
noncomputable def substitute {target oracle : List Bool → List Bool}
    (r : PfaffianPort.Complexity.PolyTimeTuringReduction target oracle)
    (h : FiniteComputer id id oracle) : FiniteComputer id id target := by
  letI := h.finiteAlphabets
  refine ⟨PfaffianPort.OracleSubstitution.substituteComputer r
    h.toTM2ComputableInPolyTime, ?_⟩
  exact PfaffianPort.OracleSubstitution.alphabetFintype r.machine h.toTM2ComputableAux

end FiniteComputer

/-- An unused natural-number scratch alphabet is permitted by mathlib's `FinTM2`.
Only the Boolean input/output stack is ever accessed. -/
def extraStackIdentity : FinTM2 where
  K := Bool
  k₀ := false
  k₁ := false
  Γ b := if b then ℕ else Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  Γk₀Fin := inferInstanceAs (Fintype Bool)
  m _ := .halt

/-- This raw timed witness computes identity in exactly one transition. -/
noncomputable def extraStackIdentityComputer :
    TM2ComputableInPolyTime (id : List Bool → List Bool) id id where
  tm := extraStackIdentity
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := 1
  outputsFun _ := {
    steps := 1
    evals_in_steps := rfl
    steps_le_m := by simp }

/-- A certificate cannot be recovered for every particular raw TM2 witness.
This says nothing against constructing a different finite-alphabet witness. -/
theorem extraStackIdentity_not_certifiable :
    ¬ Nonempty (StackAlphabetCertificate extraStackIdentity) := by
  rintro ⟨h⟩
  let : Fintype ℕ := h true
  exact Infinite.not_finite (inferInstance : Finite ℕ)

end Counting.Algorithm.Pfaffian
