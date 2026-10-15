import ComplexCSP.Complexity.CSPMarginalBounds
import ComplexCSP.Structure.WeightedMaltsevStructure
import ComplexCSP.Complexity.EncodingBounds

/-! # One-polynomial bounds for normalized marginal rows and factors

Each input row consists of a fixed number of actual marginal values, already
uniformly bounded in the original CSP code length. Actual normalization and
summation machines are applied once to this bound, never iterated by level.
-/
namespace ComplexCSP.ComplexityCSPMarginalRowBounds
open scoped BigOperators
open ComplexityCSPCode ComplexityCSPMarginalBounds ComplexityRowNormalization
open ComplexityEncodingBounds MaltsevWitness WeightedMaltsev
open PlanarHom PlanarHom.Complexity PlanarHom.MachineComposition
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)

/-- Materialized vector labels have exactly the existing executable result codec. -/
noncomputable def labelEncoding (d : ℕ) : BitEncoding (RowLabel K d) :=
  (resultEncoding basis d).retract decodeLabel materializeLabel materialize_decode

omit [DecidableEq K] in
/-- A fixed d-coordinate row has linear framing overhead in its entry bound. -/
theorem rowEncoding_length_le (v : Fin d → K) (B : ℕ)
    (h : ∀ i, ((numberFieldEncoding basis).encode (v i)).length ≤ B) :
    ((rowEncoding basis d).encode v).length ≤ (6*B+3)*d+1 := by
  have he := encoded_list_le (numberFieldEncoding basis) (List.ofFn v) B (by
    intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact h i)
  simpa only [rowEncoding,BitEncoding.vector,List.length_ofFn] using he

omit [DecidableEq K] in
/-- Every actual row at every marginal level has one common polynomial bound. -/
theorem exists_marginal_row_bound : ∃ p : Polynomial ℕ, ∀ g : Code, Valid L g →
    ∀ (k : ℕ) (hk1 : k+1 ≤ g.vertices) (a : Fin k → Fin d),
      ((rowEncoding basis d).encode (tableRows (ComplexityCSPMarginalBounds.marginal L g hk1) a)).length ≤
        p.eval (encoding.encode g).length := by
  obtain ⟨p,hp⟩ := exists_marginal_output_bound L basis
  refine ⟨Polynomial.C (6*d)*p + Polynomial.C (3*d+1),?_⟩
  intro g hg k hk1 a
  have hr := rowEncoding_length_le basis
    (tableRows (ComplexityCSPMarginalBounds.marginal L g hk1) a)
    (p.eval (encoding.encode g).length) (fun c => hp g hg (k+1) hk1 (Fin.snoc a c))
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Nat.mul_add,
    Nat.add_mul,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm,Nat.add_assoc] using hr

/-- Actual row-normalization machine, extracted from its proved FP program. -/
noncomputable def normalizeMachine := Classical.choice (fp_normalize basis (d:=d))
noncomputable def rowSumMachine := Classical.choice (fp_rowSum basis (d:=d))

/-- Exact output bound from the actual normalization machine. -/
theorem normalize_length_le (v : Fin d → K) :
    ((resultEncoding basis d).encode (normalize v)).length ≤
      (outputLengthPolynomial (normalizeMachine (d:=d) basis)).eval ((rowEncoding basis d).encode v).length :=
  encoded_output_length_le (normalizeMachine basis) v

omit [DecidableEq K] in
private theorem present_row_length_le (a : Fin d) (w : Vector K d) :
    ((rowEncoding basis d).encode (view w)).length ≤
      ((labelEncoding basis d).encode (some (a,w))).length := by
  have h := encoded_mem_le (BitEncoding.nat.prod (rowEncoding basis d))
    (List.mem_singleton_self (a.val,view w))
  rw [BitEncoding.prod_length] at h
  dsimp only at h
  change _ ≤ ((BitEncoding.nat.prod (rowEncoding basis d)).list.encode [(a.val,view w)]).length
  omega

/-- The normalized-row sum, including absent-label zero, is polynomial in the
actual label word. This bound is obtained from the proved field-sum machine. -/
noncomputable def factorPolynomial : Polynomial ℕ :=
  Polynomial.C (((numberFieldEncoding basis).encode (0 : K)).length) +
    outputLengthPolynomial (rowSumMachine (d:=d) basis)

omit [DecidableEq K] in
theorem labelFactor_length_le (r : RowLabel K d) :
    ((numberFieldEncoding basis).encode (labelFactor r)).length ≤
      (factorPolynomial (d:=d) basis).eval ((labelEncoding basis d).encode r).length := by
  cases r with
  | none =>
    simp only [labelFactor,factorPolynomial,Polynomial.eval_add,Polynomial.eval_C]
    exact Nat.le_add_right _ _
  | some p =>
    rcases p with ⟨a,w⟩
    have h := encoded_output_length_le (rowSumMachine (d:=d) basis) (view w)
    have hm := natPolynomial_monotone (outputLengthPolynomial (rowSumMachine (d:=d) basis))
      (present_row_length_le basis a w)
    change ((numberFieldEncoding basis).encode (rowSum (view w))).length ≤ _
    exact (h.trans hm).trans (by
      simp only [factorPolynomial,Polynomial.eval_add,Polynomial.eval_C]
      omega)

/-- One polynomial simultaneously bounds normalized labels and their exact
row-sum factors at every level of the original instance. -/
theorem exists_normalized_marginal_bounds : ∃ p : Polynomial ℕ, ∀ g : Code, Valid L g →
    ∀ (k : ℕ) (hk1 : k+1 ≤ g.vertices) (a : Fin k → Fin d),
      let r := tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) a
      ((labelEncoding basis d).encode r).length ≤ p.eval (encoding.encode g).length ∧
      ((numberFieldEncoding basis).encode (labelFactor r)).length ≤ p.eval (encoding.encode g).length := by
  obtain ⟨p,hp⟩ := exists_marginal_row_bound L basis
  let q := (outputLengthPolynomial (normalizeMachine (d:=d) basis)).comp p
  let r := (factorPolynomial (d:=d) basis).comp q
  refine ⟨q+r,?_⟩
  intro g hg k hk1 a
  let v := tableRows (ComplexityCSPMarginalBounds.marginal L g hk1) a
  have hnorm := normalize_length_le basis v
  have hsize := natPolynomial_monotone (outputLengthPolynomial (normalizeMachine (d:=d) basis))
    (hp g hg k hk1 a)
  have hlabel : ((labelEncoding basis d).encode
      (tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) a)).length ≤
        q.eval (encoding.encode g).length := by
    simpa only [labelEncoding,BitEncoding.retract,tableLabel,normalizedRow,decode_materialize,
      view_ofFn,q,Polynomial.eval_comp] using hnorm.trans hsize
  have hfactor := (labelFactor_length_le basis
    (tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) a)).trans
      (natPolynomial_monotone (factorPolynomial (d:=d) basis) hlabel)
  constructor
  · exact hlabel.trans (by rw [Polynomial.eval_add]; omega)
  · exact hfactor.trans (by
      simp only [r,Polynomial.eval_add,Polynomial.eval_comp]
      omega)

end ComplexCSP.ComplexityCSPMarginalRowBounds
