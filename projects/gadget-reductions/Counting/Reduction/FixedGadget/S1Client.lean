import Counting.Reduction.FixedGadget.Client

/-! A direct S1 client of the exported physical template presentation. It keeps
an isolated original hidden variable, outside the graph machine's input model. -/
namespace Counting.Reduction.FixedGadget.S1Client
open Counting.Model Counting.Gadget
open Holant.Complexity.FixedGadgetSubstitution
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000

abbrev baseLanguage := (Bridge.Holant.adapt
  (Client.binaryMacro.network Client.binaryMacro_valid Client.base Client.kernels)).language

def sourceLanguage : Language Bool ℕ Unit where
  arity _ := 2
  value _ := Client.extended 1

def gadgets : Substitution.Gadgets baseLanguage sourceLanguage := fun _ =>
  templatePresentation Client.binaryMacro Client.binaryMacro_valid Client.base Client.kernels

theorem realizes : Substitution.Realizes gadgets := by
  intro i x
  change (templatePresentation Client.binaryMacro Client.binaryMacro_valid
    Client.base Client.kernels).table x = Client.extended 1 x
  rw [templatePresentation_table]
  have h := eq_of_heq (Client.extended_realized 1)
  exact congrFun h x

def occurrence : Occurrence sourceLanguage (Fin 2 ⊕ Fin 1) :=
  ⟨(), fun i => .inl i⟩

def source : OpenInstance sourceLanguage (Fin 2) (Fin 1) :=
  ⟨[occurrence, occurrence]⟩

/-- Two independent pairs of half-edge variables, plus the isolated original one. -/
theorem fresh_hidden : (Substitution.expand gadgets source).hidden = 4 := by
  rw [Substitution.hidden_expand]
  decide

theorem total_hidden :
    Fintype.card (Fin 1 ⊕ Fin (Substitution.expand gadgets source).hidden) = 5 := by
  simp [fresh_hidden]

theorem compiled_occurrences : (Substitution.compile gadgets source).occurrences.length = 6 := by
  rw [Substitution.occurrences_length_compile]
  decide

/-- This actual S1 substitution is certified by the physical template's local value proof. -/
theorem partition (x : Fin 2 → Bool) :
    (Substitution.compile gadgets source).partition x = 2 * (Client.extended 1 x)^2 := by
  rw [Substitution.partition_compile gadgets realizes]
  revert x
  decide

theorem at_false : (Substitution.compile gadgets source).partition (fun _ => false) = 98 := by
  rw [partition]
  decide
end
end Counting.Reduction.FixedGadget.S1Client
