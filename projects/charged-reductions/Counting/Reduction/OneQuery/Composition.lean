import Counting.Reduction.OneQuery.SharpP
import PlanarHom.PromisedFPReductionClosure
import Counting.Bridge.PlanarHomSharpP

/-! # Actual promised composition and oracle elimination -/

noncomputable section
namespace Counting.Reduction.OneQuery
open PlanarHom.Complexity Counting.Computation Counting.Complexity Turing

/-- A typed solver already runs on these literal canonical words. Choosing the
represented object is used only to index its correctness proof, not as a parser
or extra computation. The underlying machine and polynomial are unchanged. -/
def canonicalSolver {α : Type} {e : BitEncoding α} {f : α → ℕ}
    (p : PolyTime e.toFinEncoding BitEncoding.nat.toFinEncoding f) :
    TM2ComputableInPolyTime (BitEncoding.bits.restrict (problem e f).valid).encode
      BitEncoding.bits.encode (fun x => (problem e f).value x.val) where
  toTM2ComputableAux := p.toTM2ComputableAux
  time := p.time
  outputsFun x := by
    let a := Classical.choose x.property
    have ha : e.encode a = x.val := Classical.choose_spec x.property
    have hv : (problem e f).value x.val = BitEncoding.nat.encode (f a) := by
      rw [← ha]
      exact value_encode e f a
    exact {
      steps := (p.outputsFun a).steps
      evals_in_steps := by
        have h := (p.outputsFun a).evals_in_steps
        dsimp only [BitEncoding.toFinEncoding, BitEncoding.restrict, BitEncoding.bits] at h ⊢
        simpa only [id_eq, hv, ha] using h
      steps_le_m := by
        have h := (p.outputsFun a).steps_le_m
        dsimp only [BitEncoding.toFinEncoding, BitEncoding.restrict, BitEncoding.bits] at h ⊢
        simpa only [id_eq, ha] using h }

@[simp] theorem canonicalSolver_time {α : Type} {e : BitEncoding α} {f : α → ℕ}
    (p : PolyTime e.toFinEncoding BitEncoding.nat.toFinEncoding f) :
    (canonicalSolver p).time = p.time := rfl

/-- Feed the new compiler into the existing nested-query composition compiler. -/
def chain {α β : Type} {ea : BitEncoding α} {eb : BitEncoding β}
    {f : α → ℕ} {g : β → ℕ} {Q : PromiseProblem}
    (r : ParsimoniousReduction ea.toFinEncoding eb.toFinEncoding f g)
    (w : SharpPWitness eb.toFinEncoding g)
    (s : PromisePolyTimeTuringReduction (problem eb g) Q) :
    PromisePolyTimeTuringReduction (problem ea f) Q := (r.toCharged w).trans s

/-- Eliminate the composed oracle using the actual promised substitution compiler;
no total solver outside the final promise is needed. -/
def substitute {α β : Type} {ea : BitEncoding α} {eb : BitEncoding β}
    {f : α → ℕ} {g : β → ℕ} {Q : PromiseProblem}
    (r : ParsimoniousReduction ea.toFinEncoding eb.toFinEncoding f g)
    (w : SharpPWitness eb.toFinEncoding g)
    (s : PromisePolyTimeTuringReduction (problem eb g) Q)
    (solver : TM2ComputableInPolyTime (BitEncoding.bits.restrict Q.valid).encode
      BitEncoding.bits.encode (fun x => Q.value x.val)) :
    TM2ComputableInPolyTime (BitEncoding.bits.restrict (problem ea f).valid).encode
      BitEncoding.bits.encode (fun x => (problem ea f).value x.val) :=
  PromisedFPClosureReconstruction.computer (chain r w s) solver

/-- Both compilers appear literally in the returned ordinary machine. -/
theorem substitute_machine {α β : Type} {ea : BitEncoding α} {eb : BitEncoding β}
    {f : α → ℕ} {g : β → ℕ} {Q : PromiseProblem}
    (r : ParsimoniousReduction ea.toFinEncoding eb.toFinEncoding f g)
    (w : SharpPWitness eb.toFinEncoding g)
    (s : PromisePolyTimeTuringReduction (problem eb g) Q)
    (solver : TM2ComputableInPolyTime (BitEncoding.bits.restrict Q.valid).encode
      BitEncoding.bits.encode (fun x => Q.value x.val)) :
    (substitute r w s solver).tm = PlanarHom.OracleSubstitution.machine
      (PlanarHom.OracleReductionComposition.composeMachine (machine r) s.machine)
      solver.toTM2ComputableAux := rfl

end Counting.Reduction.OneQuery
