import Counting.Reduction.OneQuery.Run
import PlanarHom.OraclePrecomposition

/-! # Actual preprocessing and one charged oracle call -/

noncomputable section
namespace Counting.Reduction.OneQuery
open PlanarHom.Complexity Counting.Computation Counting.Complexity

variable {α β : Type} {ea : BitEncoding α} {eb : BitEncoding β}
variable {f : α → ℕ} {g : β → ℕ}

/-- Compile the supplied public map, then query its exact materialized output. -/
def machine (r : ParsimoniousReduction ea.toFinEncoding eb.toFinEncoding f g) : OracleTM2 := by
  letI := r.machine.finiteAlphabets
  exact PlanarHom.OraclePrecomposition.machine r.machine.toTM2ComputableAux directQueryMachine

def time (r : ParsimoniousReduction ea.toFinEncoding eb.toFinEncoding f g)
    (answerBound : Polynomial ℕ) : Polynomial ℕ :=
  r.machine.time + 2 + PolyTime.outputLengthPolynomial r.machine +
    answerBound.comp (PolyTime.outputLengthPolynomial r.machine)

/-- The real machine has this exact two-phase run against every oracle, even
before requiring that the oracle answer the counting problem correctly. -/
theorem run (r : ParsimoniousReduction ea.toFinEncoding eb.toFinEncoding f g)
    (oracle : Bits → Bits) (a : α) :
    (machine r).Run oracle ((machine r).initial (ea.encode a))
      ((machine r).final (oracle (eb.encode (r.map a))))
      ((r.machine.outputsFun a).steps + 2)
      ((r.machine.outputsFun a).steps + 2 + (eb.encode (r.map a)).length +
        (oracle (eb.encode (r.map a))).length)
      [(eb.encode (r.map a), oracle (eb.encode (r.map a)))] := by
  letI := r.machine.finiteAlphabets
  let out := r.machine.outputsFun a
  have h := PlanarHom.OraclePrecomposition.run r.machine.toTM2ComputableAux directQueryMachine
    (ea.encode a) (eb.encode (r.map a)) (oracle (eb.encode (r.map a))) _ out
    (directQueryMachine_run oracle (eb.encode (r.map a)))
  simpa only [machine, out, Nat.add_assoc] using h

/-- Every complete run has the same single query/answer transcript and exact
cost. Uniqueness is a theorem of the existing deterministic transition relation. -/
theorem complete_run_unique (r : ParsimoniousReduction ea.toFinEncoding eb.toFinEncoding f g)
    (oracle : Bits → Bits) (a : α) (answer : Bits) {steps cost : ℕ} {qs : OracleTM2.Transcript}
    (h : (machine r).Run oracle ((machine r).initial (ea.encode a))
      ((machine r).final answer) steps cost qs) :
    steps = (r.machine.outputsFun a).steps + 2 ∧
    cost = (r.machine.outputsFun a).steps + 2 + (eb.encode (r.map a)).length +
      (oracle (eb.encode (r.map a))).length ∧
    qs = [(eb.encode (r.map a), oracle (eb.encode (r.map a)))] := by
  have huniq := run_unique h (run r oracle a) (step_final _ _ _) (step_final _ _ _)
  exact huniq.2

/-- Correct extending oracles produce the exact original count, on the same run. -/
theorem run_correct (r : ParsimoniousReduction ea.toFinEncoding eb.toFinEncoding f g)
    (oracle : Bits → Bits) (extension : ∀ q, (problem eb g).valid q → oracle q = (problem eb g).value q)
    (a : α) :
    (machine r).Run oracle ((machine r).initial (ea.encode a))
      ((machine r).final (BitEncoding.nat.encode (f a)))
      ((r.machine.outputsFun a).steps + 2)
      ((r.machine.outputsFun a).steps + 2 + (eb.encode (r.map a)).length +
        (BitEncoding.nat.encode (g (r.map a))).length)
      [(eb.encode (r.map a), BitEncoding.nat.encode (g (r.map a)))] := by
  have ho : oracle (eb.encode (r.map a)) = BitEncoding.nat.encode (g (r.map a)) :=
    (extension _ (valid_encode eb g _)).trans (value_encode eb g _)
  simpa only [ho, r.correct a] using run r oracle a

theorem cost_le (r : ParsimoniousReduction ea.toFinEncoding eb.toFinEncoding f g)
    (answerBound : Polynomial ℕ)
    (bound : ∀ b, (BitEncoding.nat.encode (g b)).length ≤ answerBound.eval (eb.encode b).length)
    (a : α) :
    (r.machine.outputsFun a).steps + 2 + (eb.encode (r.map a)).length +
        (BitEncoding.nat.encode (g (r.map a))).length ≤
      (time r answerBound).eval (ea.encode a).length := by
  have hs := (r.machine.outputsFun a).steps_le_m
  have hq : (eb.encode (r.map a)).length ≤
      (PolyTime.outputLengthPolynomial r.machine).eval (ea.encode a).length :=
    r.map_encoded_length_le a
  have ha := (bound (r.map a)).trans (PlanarHom.MachineComposition.natPolynomial_monotone answerBound hq)
  change (r.machine.outputsFun a).steps ≤ r.machine.time.eval (ea.encode a).length at hs
  simpa only [time, Polynomial.eval_add, Polynomial.eval_ofNat, Polynomial.eval_comp] using
    Nat.add_le_add (Nat.add_le_add (Nat.add_le_add_right hs 2) hq) ha

/-- Public maps become the existing charged promised-reduction object. The only
extra premise is an answer-size bound, not an algorithm for the target count. -/
def compile (r : ParsimoniousReduction ea.toFinEncoding eb.toFinEncoding f g)
    (answerBound : Polynomial ℕ)
    (bound : ∀ b, (BitEncoding.nat.encode (g b)).length ≤ answerBound.eval (eb.encode b).length) :
    PromisePolyTimeTuringReduction (problem ea f) (problem eb g) where
  machine := machine r
  time := time r answerBound
  computes oracle ho raw valid := by
    obtain ⟨a, rfl⟩ := valid
    refine ⟨(r.machine.outputsFun a).steps + 2, _,
      [(eb.encode (r.map a), BitEncoding.nat.encode (g (r.map a)))],
      ?_, cost_le r answerBound bound a, ?_⟩
    · simpa only [value_encode] using run_correct r oracle ho a
    · intro q ans h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (List.mem_singleton.mp h)
      exact valid_encode eb g _

end Counting.Reduction.OneQuery
