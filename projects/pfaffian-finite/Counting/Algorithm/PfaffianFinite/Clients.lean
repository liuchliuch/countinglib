import Counting.Algorithm.PfaffianFinite
import Counting.Algorithm.Pfaffian.Examples

/-!
# Clients of the complete finite-alphabet endpoint

The ternary codec exercises the genuinely generalized external-alphabet wrapper.
The old infinite-scratch counterexample now acquires a finite refined witness,
without contradicting its original non-certifiability. Rational clients use the
complete variable-order Pfaffian machine and the original exact number-field codec.
-/

noncomputable section

namespace Counting.Algorithm.PfaffianFinite.Clients

open Turing
open Counting.Algorithm.Pfaffian

/-- A faithful non-Boolean external encoding: the input word itself. -/
def ternaryEncoding : Computability.Encoding (List (Fin 3)) (Fin 3) where
  encode := id
  decode := some
  decode_encode _ := rfl

/-- The generic wrapper applies beyond the source compiler's Boolean codecs. -/
def ternaryComputer : Counting.Computation.PolyTime ternaryEncoding ternaryEncoding id :=
  Counting.Computation.FiniteSupport.toPolyTime
    (idComputableInPolyTime (id : List (Fin 3) → List (Fin 3)))

theorem ternary_steps (xs : List (Fin 3)) : (ternaryComputer.outputsFun xs).steps = 1 := rfl

/-- Repair the old concrete witness with a genuinely different, finite machine. -/
def repairedScratchComputer :
    FiniteComputer (id : List Bool → List Bool) id id := refine extraStackIdentityComputer

theorem repairedScratch_steps (xs : List Bool) :
    (repairedScratchComputer.outputsFun xs).steps = 1 := rfl

/-- Compiling a finite implementation never makes the old infinite type finite. -/
theorem source_still_not_certifiable :
    ¬ Nonempty (StackAlphabetCertificate extraStackIdentity) :=
  extraStackIdentity_not_certifiable

/-- The refined unused natural-number scratch alphabet is actually empty. -/
theorem repairedScratch_empty :
    IsEmpty (repairedScratchComputer.tm.Γ true) := by
  refine ⟨?_⟩
  intro a
  rcases a with ⟨a, ha⟩
  change (⟨true, a⟩ : Sigma extraStackIdentity.Γ) ∈
    (Set.range (Sigma.mk false) ∪ Set.range (Sigma.mk false)) ∪
      ⋃ (_ : Unit), (∅ : Set (Sigma extraStackIdentity.Γ)) at ha
  rcases ha with (⟨b, hb⟩ | ⟨b, hb⟩) | ha
  · have hh := congrArg Sigma.fst hb
    cases hh
  · have hh := congrArg Sigma.fst hb
    cases hh
  · obtain ⟨_, h⟩ := Set.mem_iUnion.mp ha
    exact h

/-- A full F1 certificate, with matrix order carried by the nested-list input. -/
def rationalComputer : Counting.Computation.PolyTime
    (gridEncoding (Module.Basis.singleton (Fin 1) ℚ)).toFinEncoding
    (PfaffianPort.Complexity.numberFieldEncoding (Module.Basis.singleton (Fin 1) ℚ)).toFinEncoding
    (evaluateGrid (K := ℚ)) :=
  evaluateGridPolyTime (Module.Basis.singleton (Fin 1) ℚ)

theorem rational_inFP : Counting.Computation.InFP
    (gridEncoding (Module.Basis.singleton (Fin 1) ℚ)).toFinEncoding
    (PfaffianPort.Complexity.numberFieldEncoding (Module.Basis.singleton (Fin 1) ℚ)).toFinEncoding
    (evaluateGrid (K := ℚ)) := ⟨rationalComputer⟩

set_option backward.isDefEq.respectTransparency false in
/-- An actual complete-machine run whose output word encodes the negative
Pfaffian -29; this input forces a pivot swap and nonintegral Schur arithmetic. -/
def rationalPivotRun : TM2OutputsInTime rationalComputer.tm
    (((gridEncoding (Module.Basis.singleton (Fin 1) ℚ)).toFinEncoding.encode
      (matrixRows Examples.pivotSwapMatrix)).map rationalComputer.inputAlphabet.invFun)
    (some (((PfaffianPort.Complexity.numberFieldEncoding
      (Module.Basis.singleton (Fin 1) ℚ)).toFinEncoding.encode (-29)).map rationalComputer.outputAlphabet.invFun))
    (rationalComputer.time.eval
      ((gridEncoding (Module.Basis.singleton (Fin 1) ℚ)).toFinEncoding.encode
        (matrixRows Examples.pivotSwapMatrix)).length) := by
  have h := rationalComputer.outputsFun (matrixRows Examples.pivotSwapMatrix)
  simpa only [Examples.pivot_swap_grid] using h

set_option backward.isDefEq.respectTransparency false in
/-- A second complete-machine run covers normalization of a ragged grid with a
nonzero diagonal and inconsistent lower triangle, without an input promise. -/
def rationalRaggedRun : TM2OutputsInTime rationalComputer.tm
    (((gridEncoding (Module.Basis.singleton (Fin 1) ℚ)).toFinEncoding.encode
      ([[99, 3], [7]] : Grid ℚ)).map rationalComputer.inputAlphabet.invFun)
    (some (((PfaffianPort.Complexity.numberFieldEncoding
      (Module.Basis.singleton (Fin 1) ℚ)).toFinEncoding.encode 3).map rationalComputer.outputAlphabet.invFun))
    (rationalComputer.time.eval
      ((gridEncoding (Module.Basis.singleton (Fin 1) ℚ)).toFinEncoding.encode
        ([[99, 3], [7]] : Grid ℚ)).length) := by
  have h := rationalComputer.outputsFun ([[99, 3], [7]] : Grid ℚ)
  simpa only [Examples.ragged_grid] using h

end Counting.Algorithm.PfaffianFinite.Clients
