import Counting.Algorithm.VariableEliminationWork.Cost

namespace Counting.Algorithm.VariableEliminationWork
open Counting.Algorithm.VariableEliminationLayout
namespace Work

/-- Componentwise multiplication by a number of repeated executed observations. -/
def scale (n : Nat) (w : Work) : Work where
  reads := {
    coordinateCases := n * w.reads.coordinateCases
    colourCases := n * w.reads.colourCases
    colourComparisons := n * w.reads.colourComparisons
    indexIncrements := n * w.reads.indexIncrements
    hornerAdditions := n * w.reads.hornerAdditions
    hornerMultiplications := n * w.reads.hornerMultiplications
    arrayReads := n * w.reads.arrayReads
  }
  coefficientAdditions := n * w.coefficientAdditions
  coefficientMultiplications := n * w.coefficientMultiplications
  oracleCalls := n * w.oracleCalls
  listCases := n * w.listCases
  listCons := n * w.listCons
  nilResults := n * w.nilResults
  arrayPushes := n * w.arrayPushes
  arrayConstructions := n * w.arrayConstructions
  natIncrements := n * w.natIncrements
  generationTests := n * w.generationTests
  layoutConstructions := n * w.layoutConstructions
  cacheConstructions := n * w.cacheConstructions
  closureConstructions := n * w.closureConstructions

@[simp] theorem scale_zero (w : Work) : scale 0 w = zero := by
  simp [scale, zero, ReadWork.zero]

@[simp] theorem scale_succ (n : Nat) (w : Work) : scale (n + 1) w = w.add (scale n w) := by
  simp [scale, add, ReadWork.add, Nat.add_mul, Nat.add_comm]

theorem sum_const {A : Type} (xs : List A) (w : Work) :
    sum (xs.map (fun _ => w)) = scale xs.length w := by
  induction xs <;> simp only [List.map_nil, List.map_cons, List.length_nil, List.length_cons, sum, scale_zero, scale_succ, *]

@[simp] theorem reads_sum (xs : List Work) :
    (sum xs).reads = ReadWork.sum (xs.map (fun w => w.reads)) := by
  induction xs <;> simp [sum, add, zero, ReadWork.sum, *]

end Work
end Counting.Algorithm.VariableEliminationWork
