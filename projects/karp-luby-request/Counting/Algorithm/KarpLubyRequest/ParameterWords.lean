import Counting.Algorithm.KarpLubyRequest.NaturalWords
import Counting.Algorithm.KarpLubyRequest.Embedded

/-!
# Physical preparation of a retained raw parameter word

The caller preserves the original field, makes a charged two-pass copy, then
runs the exact total raw-natural canonicalizer on that copy. All scratch is
empty on return. This stage is reused for all four accuracy/confidence number
fields; the input bits are not assumed to encode a canonical natural.
-/
namespace Counting.Algorithm.KarpLubyRequest.ParameterWords
open Turing Computability Holant.Complexity StackProtocol
variable {K Λ τ : Type} [DecidableEq K]

/-- Retained original, disposable copy, canonical destination, temporary. -/
abbrev Stacks (K : Type) := Fin 4 ↪ K

structure Labels (Λ : Type) where
  copy : Λ
  copyRestore : Λ
  move : Λ
  highest : Λ
  restore : Λ
  next : Λ

def naturalMap (st : Stacks K) : NaturalWords.Stacks K :=
  ⟨fun i => st (![1, 2, 3] i), by
    intro a b h
    have hi := st.injective h
    fin_cases a <;> fin_cases b <;> simp_all⟩
@[simp] theorem natural_zero (st : Stacks K) : naturalMap st 0 = st 1 := rfl
@[simp] theorem natural_one (st : Stacks K) : naturalMap st 1 = st 2 := rfl
@[simp] theorem natural_two (st : Stacks K) : naturalMap st 2 = st 3 := rfl

def naturalLabels (lab : Labels Λ) : NaturalWords.Labels Λ :=
  ⟨lab.move, lab.highest, lab.restore, lab.next⟩

structure Executes (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (st : Stacks K) (lab : Labels Λ) : Prop where
  copy : ExecutesAt step lab.copy (copyMoveStmt (st 0) (st 3) lab.copy lab.copyRestore)
  copyRestore : ExecutesAt step lab.copyRestore
    (copyRestoreStmt (st 0) (st 1) (st 3) lab.copyRestore lab.move)
  natural : NaturalWords.Executes step (naturalMap st) (naturalLabels lab)

def tapes (st : Stacks K) (frame : K → List Bool) (original raw canonical scratch : List Bool) : K → List Bool :=
  Function.update (Function.update (Function.update (Function.update frame (st 0) original)
    (st 1) raw) (st 2) canonical) (st 3) scratch

private theorem as_copy (st : Stacks K) (frame : K → List Bool)
    (original raw canonical scratch : List Bool) :
    tapes st frame original raw canonical scratch =
      tapes3 (Function.update frame (st 2) canonical) (st 0) (st 1) (st 3) original raw scratch := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
    by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
    simp_all [tapes, tapes3, Function.update_apply, st.injective.eq_iff]

private theorem as_natural (st : Stacks K) (frame : K → List Bool)
    (original raw canonical scratch : List Bool) :
    tapes st frame original raw canonical scratch =
      NaturalWords.tapes (naturalMap st) (Function.update frame (st 0) original)
        raw canonical scratch := by
  funext k
  by_cases h0 : k = st 0 <;> by_cases h1 : k = st 1 <;>
    by_cases h2 : k = st 2 <;> by_cases h3 : k = st 3 <;>
    simp_all [tapes, NaturalWords.tapes, tapes3, Function.update_apply, st.injective.eq_iff]

/-- Copying and normalization are one returning execution, with every original
bit and every additional canonical high bit handled by finite stack code. -/
theorem prepare_exact (step : Cfg K Λ τ → Option (Cfg K Λ τ)) (st : Stacks K) (lab : Labels Λ)
    (exec : Executes step st lab) (memory : τ) (frame : K → List Bool) (raw : List Bool) :
    RunsExactly step (cfg lab.copy memory (tapes st frame raw [] [] []))
      (cfg lab.next memory (tapes st frame raw [] (encodeNat (decodeNat raw)) []))
      (4 * raw.length + 5) := by
  have hc : RunsExactly step (cfg lab.copy memory (tapes st frame raw [] [] []))
      (cfg lab.move memory (tapes st frame raw raw [] [])) (2 * (raw.length + 1)) := by
    simpa only [← as_copy, List.append_nil] using
      copy_exact_frame (st 0) (st 1) (st 3)
        (fun h => by have := st.injective h; contradiction)
        (fun h => by have := st.injective h; contradiction)
        (fun h => by have := st.injective h; contradiction)
        step lab.copy lab.copyRestore lab.move exec.copy exec.copyRestore memory
        (Function.update frame (st 2) []) raw []
  have hn : RunsExactly step (cfg lab.move memory (tapes st frame raw raw [] []))
      (cfg lab.next memory (tapes st frame raw [] (encodeNat (decodeNat raw)) []))
      (2 * raw.length + 3) := by
    simpa only [← as_natural, naturalLabels, NaturalWords.canonicalize_eq, List.append_nil] using
      NaturalWords.canonicalize_exact step (naturalMap st) (naturalLabels lab) exec.natural memory
        (Function.update frame (st 0) raw) raw []
  convert hc.trans hn using 1 <;> omega

end Counting.Algorithm.KarpLubyRequest.ParameterWords
