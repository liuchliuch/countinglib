import Paper2.ExactInput.FixedRootCodec.EuclideanPolynomial
import Paper2.Complexity.BellMachines.FixedGadgetSubstitution.Compiler.Lists

/-! Actual fixed-degree negative Euclidean chains. All polynomial
coefficients and the evaluation point remain runtime inputs. The finite
chain is padded with zeros after termination; its length is a program
constant. This module supplies programs, not a presumed root-count oracle. -/
namespace Paper2.ExactInput.FixedRootCodec.VariablePolynomial
open Computability Paper2.Algebraic Paper2.Complexity
open BinaryCompose FixedFieldMachines BellMachines Polynomial
open FixedGadgetSubstitution.Compiler
noncomputable section

def negateComputes (n : ℕ) :
    Computes (vectorEncoding n) (vectorEncoding n) (fun v : Fin n → ℚ => -v) :=
  assembleComputes _ n _ (fun i => congrComputes
    (rationalProvider.mulComputes (constantComputes _ rationalEncoding (-1))
      (coordinateComputes n i)) (fun v => by simp))

def euclideanStep {n : ℕ} (p : Pair n) : Pair n :=
  if p.2 = 0 then (0,0) else (p.2,-remainder p)

def euclideanStepComputes (n : ℕ) :
    Computes (pairVectorEncoding n) (pairVectorEncoding n) (euclideanStep (n := n)) :=
  congrComputes (ifComputes
    ((Wiring.secondComputes _ _).andThen (FixedRootCodec.zeroComputes (vectorEncoding n)))
    (constantComputes _ _ (0,0))
    (pairComputes (Wiring.secondComputes _ _)
      ((remainderComputes n).andThen (negateComputes n))))
      (fun p => by simp only [euclideanStep,Function.comp_apply,decide_eq_true_eq])

def initialComputes (n : ℕ) :
    Computes (vectorEncoding n) (pairVectorEncoding n)
      (fun v : Fin n → ℚ => (v,derivative v)) :=
  pairComputes (identityComputes _) (derivativeComputes n)

def stage {n : ℕ} (v : Fin n → ℚ) : ℕ → Pair n
  | 0 => (v,derivative v)
  | k+1 => euclideanStep (stage v k)

def stageComputes (n : ℕ) : (k : ℕ) →
    Computes (vectorEncoding n) (pairVectorEncoding n) (fun v => stage v k)
  | 0 => initialComputes n
  | k+1 => congrComputes ((stageComputes n k).andThen (euclideanStepComputes n))
      (fun _ => rfl)

def term {n : ℕ} (v : Fin n → ℚ) (k : ℕ) : Fin n → ℚ := (stage v k).1

def termComputes (n k : ℕ) :
    Computes (vectorEncoding n) (vectorEncoding n) (fun v => term v k) :=
  congrComputes ((stageComputes n k).andThen (Wiring.firstComputes _ _)) (fun _ => rfl)

def chain {n : ℕ} (v : Fin n → ℚ) : List (Fin n → ℚ) :=
  (List.range (n+2)).map (term v)

def chainComputes (n : ℕ) :
    Computes (vectorEncoding n) (framedListEncoding (vectorEncoding n)) (chain (n := n)) :=
  fixedListComputes _ _ term (termComputes n) (List.range (n+2))

theorem negate_polynomial {n : ℕ} (v : Fin n → ℚ) :
    polynomial (-v) = -polynomial v := by
  simp [polynomial,Pi.neg_apply,monomial_neg,Finset.sum_neg_distrib]

theorem euclideanStep_polynomial {n : ℕ} (p : Pair n) (h : p.2 ≠ 0) :
    polynomial (euclideanStep p).1 = polynomial p.2 ∧
      polynomial (euclideanStep p).2 = -(polynomial p.1 % polynomial p.2) := by
  simp only [euclideanStep,h,ite_false]
  exact ⟨trivial,by rw [negate_polynomial,remainder_polynomial]⟩

def rationalSign (q : ℚ) : ℚ := if q = 0 then 0 else if q < 0 then -1 else 1

def rationalSignComputes : Computes rationalEncoding rationalEncoding rationalSign :=
  congrComputes (ifComputes (FixedRootCodec.zeroComputes rationalEncoding)
    (constantComputes _ _ 0)
    (ifComputes rationalNegativeComputes (constantComputes _ _ (-1))
      (constantComputes _ _ 1)))
      (fun q => by simp only [rationalSign,decide_eq_true_eq])

def termSign {n : ℕ} (p : (Fin n → ℚ) × ℚ) (k : ℕ) : ℚ :=
  rationalSign (evaluation (term p.1 k) p.2)

def termSignComputes (n k : ℕ) :
    Computes (inputEncoding n) rationalEncoding (fun p => termSign p k) :=
  congrComputes ((pairComputes
    ((Wiring.firstComputes _ _).andThen (termComputes n k)) (Wiring.secondComputes _ _)).andThen
      ((evaluationComputes n).andThen rationalSignComputes)) (fun _ => rfl)

end
end Paper2.ExactInput.FixedRootCodec.VariablePolynomial
