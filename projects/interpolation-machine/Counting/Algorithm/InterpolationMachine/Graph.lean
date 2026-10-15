import Counting.Algorithm.InterpolationMachine.Postprocessor
import Holant.Proofs.BinaryInterpolation.MachineCapstone

/-!
# Graph-specialized polynomial bounds and the public recovery value

Here the answer-size premises are discharged by the actual fixed-table graph
queries. The postprocessor's time polynomial is evaluated in the original graph
code length. This is a graph-specific oracle reduction, not arbitrary-node FP.
-/
namespace Counting.Algorithm.InterpolationMachine.Graph

open Turing Computability Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryInterpolation Holant.Complexity.BinaryCompose
open Holant.OneHot.StackProgram Holant.OneHot.StackProgram.Machine
namespace MC
export Holant.LocalDrafts.BinaryInterpolation.MachineCapstone
  (Data Input inputEncoding answerEncoding queryEncoding queries count code values answered
   resultPair interpolatedValue denominator post postTime machine timePolynomial
   widthPolynomial structuralPolynomial literalCoordinates interpreter arithmetic
   certified post_outputs execution exact_calls_and_primitive reduction)
end MC
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {n s b : ℕ} {arity : ℕ → ℕ}
variable {F : FixedField K n} {T : ExactSignatureTables n s b arity} (d : MC.Data F T)

/-- Public arithmetic recovery of exactly the ordered emitted graph answers. -/
def value (r : MC.Input d) : K :=
  Interpolation.evaluate (nodes d.geometric d.rho (MC.count d r))
    (normalized d.gamma (MC.count d r) (MC.values d r))

theorem interpolated_eq_result (r : MC.Input d) :
    MC.interpolatedValue d r =
      result d.gamma d.rho d.geometric (MC.count d r) (MC.values d r) := rfl

theorem resultPair_eq (r : MC.Input d) :
    MC.resultPair d r =
      InterpolationMachine.resultPair d.gamma d.rho d.geometric (MC.count d r) (MC.values d r) := rfl

/-- The graph-independent postprocessor above is the arithmetic machine in H1. -/
theorem arithmetic_eq : MC.arithmetic d = Postprocessor.machine F d.gamma d.rho := rfl

theorem interpolated_eq_value (r : MC.Input d)
    (hn : Function.Injective (nodes d.geometric d.rho (MC.count d r))) (hg : d.gamma ≠ 0) :
    MC.interpolatedValue d r = value d r := by
  exact result_eq_evaluate d.gamma d.rho d.geometric (MC.count d r) (MC.values d r) hn hg

/-- Every graph-derived intermediate stack word has a polynomial bit bound. -/
theorem intermediate_width (r : MC.Input d) :
    ∀ x ∈ Holant.LocalDrafts.BinaryInterpolation.PostprocessBounds.trace
      d.gamma d.rho d.geometric (MC.count d r) (MC.values d r),
      (F.encoding.encode x).length ≤
        (MC.widthPolynomial d).eval ((MC.inputEncoding d).encode r).length := by
  intro x hx
  have hq := Holant.LocalDrafts.BinaryInterpolation.MachineCapstone.structural_bounds d r
  have hu := Holant.LocalDrafts.BinaryInterpolation.OracleAnswerBounds.decode_unit F T d.gamma d.rho
  have hy := Holant.LocalDrafts.BinaryInterpolation.OracleAnswerBounds.sample_answers_bound
    F T d.gamma d.rho d.template d.valid d.binary d.edge r
  have hl := Holant.LocalDrafts.BinaryInterpolation.OracleAnswerBounds.literal_bound F T d.gamma d.rho
  have ht := Holant.LocalDrafts.BinaryInterpolation.PostprocessBounds.trace_bound F
    (Holant.LocalDrafts.BinaryInterpolation.MachineCapstone.base d) (.inl 3) hu
    d.gamma d.rho hl d.geometric (MC.count d r)
    ((Holant.LocalDrafts.BinaryInterpolation.MachineCapstone.answerBudget d).eval
      ((MC.inputEncoding d).encode r).length) (MC.values d r) hy x hx
  rw [Holant.LocalDrafts.BinaryInterpolation.MachineCapstone.width_eval]
  exact (ht.mono (.inl 3) hu hq.2.2.1).encoded_length_le F _

/-- The full Boolean postprocessor physically reorders, interprets, divides and
returns the public value, in polynomial time measured from the original graph. -/
def post_outputs_value (r : MC.Input d)
    (hn : Function.Injective (nodes d.geometric d.rho (MC.count d r))) (hg : d.gamma ≠ 0) :
    TM2OutputsInTime (MC.post d).computer
      ((MC.answerEncoding (F:=F)).encode (MC.answered d r))
      (some (F.encoding.encode (value d r)))
      ((MC.postTime d).eval ((MC.inputEncoding d).encode r).length) := by
  rw [← interpolated_eq_value d r hn hg]
  exact MC.post_outputs d r

@[instance_reducible] def finitePostAlphabets : ∀ k, Fintype ((MC.post d).computer.Γ k) :=
  fun _ => inferInstanceAs (Fintype Bool)

/-- The same oracle machine now exposes the public evaluator as its source
function; all node and scale promises remain explicit. -/
def reduction (hn : ∀ m, Function.Injective (nodes d.geometric d.rho m)) (hg : d.gamma ≠ 0) :
    PolyTimeOracleReduction (MC.inputEncoding d) F.encoding
      (MC.queryEncoding (s:=s) (b:=b) (arity:=arity)) F.encoding (value d) (T.evaluate F) where
  machine := MC.machine d
  time := MC.timePolynomial d
  correct oracle ho r := by
    rw [← interpolated_eq_value d r (hn _) hg]
    exact (MC.reduction d).correct oracle ho r

/-- The ordered transcript is on the very execution returning the public value. -/
theorem execution (hn : ∀ m, Function.Injective (nodes d.geometric d.rho m)) (hg : d.gamma ≠ 0)
    (oracle : List Bool → List Bool)
    (ho : RepresentsOracle (MC.queryEncoding (s:=s) (b:=b) (arity:=arity)) F.encoding
      (T.evaluate F) oracle) (r : MC.Input d) :
    ∃ t ≤ (MC.timePolynomial d).eval ((MC.inputEncoding d).encode r).length,
      OracleBatch.RunsTrace (MC.machine d) oracle
        ((MC.machine d).init ((MC.inputEncoding d).encode r))
        ((MC.machine d).output (F.encoding.encode (value d r))) t
        ((MC.queries d r).map (MC.queryEncoding (s:=s) (b:=b) (arity:=arity)).encode) := by
  rw [← interpolated_eq_value d r (hn _) hg]
  exact MC.execution d oracle ho r

end
end Counting.Algorithm.InterpolationMachine.Graph
