import ComplexCSP.Complexity.TypeStackExecution
import ComplexCSP.Structure.MaltsevTypeStackBitBounds

/-! # Fully compiled raw type queries with explicit polynomial budgets

The query contains ordinary context data, a unary prefix length, and a target
word. This prepares an empty continuation stack/cache and projects the actual
bounded run's returned label list and cache. Correctness on generated marginal
contexts is supplied by the separate source trace/cap theorem.
-/
namespace ComplexCSP.ComplexityTypeQuery
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityWitnessPrimitives ComplexityTypeStackMachines MaltsevTypeStack
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Fin d → Fin d → Fin d → Fin d)

abbrev Query (K : Type) := ComplexityTypeStackConcrete.Context K × (ℕ × List ℕ)
noncomputable def queryCode : BitEncoding (Query K) :=
  (ComplexityTypeStackConcrete.contextCode basis).prod (BitEncoding.unaryNat.prod wordCode)

noncomputable def preparedCode := ComplexityTypeStackExecution.inputCode (d:=d) basis

def prepare (q : Query K) : ComplexityTypeStackConcrete.Context K × State (WeightedMaltsev.RowLabel K d) :=
  (q.1,callState q.2.1 q.2.2 [] [])

omit [DecidableEq K] in
theorem fp_prepare : FP (queryCode basis) (preparedCode (d:=d) basis) (prepare (d:=d)) := by
  let ec := ComplexityTypeStackConcrete.contextCode basis
  let e := ComplexityCSPMarginalRowBounds.labelEncoding basis d
  let ei := queryCode basis
  have hc := fp_fst ec (BitEncoding.unaryNat.prod wordCode)
  have hq := fp_snd ec (BitEncoding.unaryNat.prod wordCode)
  have hn := hq.comp (fp_fst BitEncoding.unaryNat wordCode)
  have hw := hq.comp (fp_snd BitEncoding.unaryNat wordCode)
  have hs := fp_buildState ei e _ _ _ _ _ _ (fp_const ei BitEncoding.bool false) hn hw
    (fp_const ei e.list []) (fp_const ei (frameCode e).list [])
    (fp_const ei (ComplexityTypeCache.cacheEncoding e) [])
  exact hc.pair hs

noncomputable def timePolynomial (d : ℕ) : Polynomial ℕ :=
  2*(1+Polynomial.C d*((Polynomial.X+1)*Polynomial.C d))

@[simp] theorem timePolynomial_eval (d n : ℕ) :
    (timePolynomial d).eval n = 2*(1+d*((n+1)*d)) := by simp [timePolynomial]

noncomputable def executeWithSpace (space : Polynomial ℕ) (q : Query K) :
    List (WeightedMaltsev.RowLabel K d) × MaltsevWitness.ListTypeCache (WeightedMaltsev.RowLabel K d) :=
  let result := ComplexityTypeStackExecution.run L basis m
    space (timePolynomial d) (prepare q)
  (result.returnedLabels,result.cache)

/-- Every control, cache and callback operation is the actual proved bit machine. -/
theorem fp_executeWithSpace (space : Polynomial ℕ) :
    FP (queryCode basis)
      ((ComplexityCSPMarginalRowBounds.labelEncoding basis d).list.prod
        (ComplexityTypeCache.cacheEncoding (ComplexityCSPMarginalRowBounds.labelEncoding basis d)))
      (executeWithSpace L basis m space) := by
  let e := ComplexityCSPMarginalRowBounds.labelEncoding basis d
  have hr := (fp_prepare (d:=d) basis).comp
    (ComplexityTypeStackExecution.fp_run L basis m
      space (timePolynomial d))
  exact hr.comp ((fp_returnedLabels e).pair (fp_cache e))

noncomputable def execute (labelPolynomial : Polynomial ℕ) (q : Query K) :=
  executeWithSpace L basis m (MaltsevTypeStack.statePolynomial d labelPolynomial) q

theorem fp_execute (labelPolynomial : Polynomial ℕ) :
    FP (queryCode basis)
      ((ComplexityCSPMarginalRowBounds.labelEncoding basis d).list.prod
        (ComplexityTypeCache.cacheEncoding (ComplexityCSPMarginalRowBounds.labelEncoding basis d)))
      (execute L basis m labelPolynomial) :=
  fp_executeWithSpace L basis m (MaltsevTypeStack.statePolynomial d labelPolynomial)

omit [DecidableEq K] in
/-- The original instance's full encoded word is physically retained in context. -/
theorem original_length_le_prepared (q : Query K) :
    (ComplexityCSPCode.encoding.encode q.1.1.1).length ≤
      ((preparedCode (d:=d) basis).encode (prepare q)).length := by
  simp only [preparedCode, ComplexityTypeStackExecution.inputCode, prepare,
    ComplexityTypeStackConcrete.contextCode, ComplexityTypeRowCallback.contextCode,
    BitEncoding.prod_length]
  omega

omit [DecidableEq K] in
/-- The current dimension is explicitly unary, not an uncharged binary bound. -/
theorem dimension_le_prepared (q : Query K) : q.1.2.1 ≤
    ((preparedCode (d:=d) basis).encode (prepare q)).length := by
  simp only [preparedCode, ComplexityTypeStackExecution.inputCode, prepare,
    ComplexityTypeStackConcrete.contextCode, ComplexityTypeRowCallback.contextCode,
    BitEncoding.prod_length,BitEncoding.unaryNat_length]
  omega

end ComplexCSP.ComplexityTypeQuery
