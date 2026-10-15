import ComplexCSP.Structure.MaltsevTypeStackBitBounds
import ComplexCSP.Complexity.CSPMarginalCacheBounds

/-! # An original-instance polynomial cap for genuine marginal type searches

This instantiates the generic control-state bound with literal CSP prefix
marginals, their proved fixed-field bit bound and the proved BO class bound.
The polynomial depends only on the fixed language/field presentation, and its
argument is the original CSP codeword length, never the evolving state size.
-/
namespace ComplexCSP.MaltsevTypeStack
open MaltsevWitness MaltsevRelations WeightedMaltsev ComplexityWitnessEncoding
open ComplexityCSPMarginalBounds ComplexityCSPMarginalRowBounds ComplexityCSPMarginalCacheBounds
open ComplexityCSPCode ComplexityTypeStackMachines
open PlanarHom PlanarHom.Complexity
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}

/-- Uniform bit cap for every reached state up to the genuine polynomial
transition budget, across all marginal levels of the original instance. -/
theorem exists_marginal_stack_output_bound (L : Language (Fin d) K (Fin s))
    (basis : Module.Basis (Fin dimension) ℚ K) : ∃ p : Polynomial ℕ,
    ∀ (g : ComplexityCSPCode.Code), Valid L g →
    ∀ (k : ℕ) (hk1 : k+1 ≤ g.vertices) (m : Operation (Fin d)) (W : StoredCode d k),
      Correct W.toCode (rowSupport (ComplexityCSPMarginalBounds.marginal L g hk1)) →
      Preserves m (rowSupport (ComplexityCSPMarginalBounds.marginal L g hk1)) →
    ∀ (σ : K →+* ℂ),
      BlockOrthogonality.BlockOrthogonal (fun x a => σ (tableRows (ComplexityCSPMarginalBounds.marginal L g hk1) x a)) →
    ∀ (labelRaw : List ℕ → RowLabel K d),
      (∀ x, labelRaw (word x) = tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x)) →
    ∀ (len : ℕ), len ≤ k → ∀ (target : Tuple (Fin d) k) (state : State (RowLabel K d)) (t : ℕ),
      t ≤ 2*(1+d*((k+1)*d)) →
      Runs (step k (List.range d) (storedReconstruct m W) labelRaw)
        (callState len (word target) [] []) state t →
      ((stateCode (labelEncoding basis d)).encode state).length ≤ p.eval (encoding.encode g).length := by
  obtain ⟨p,hp⟩ := exists_normalized_marginal_bounds L basis
  refine ⟨statePolynomial d p,?_⟩
  intro g hg k hk1 m W hW hR σ hBO labelRaw hlab len hlen target state t ht hrun
  let G := ComplexityCSPMarginalBounds.marginal L g hk1
  let U := presentLabels G
  let N := (encoding.encode g).length
  have hlabels : ∀ a ∈ U, ((labelEncoding basis d).encode a).length ≤ p.eval N := by
    intro a ha
    obtain ⟨x,hx⟩ := present_label_realized G a ha
    rw [← hx]
    exact (hp g hg k hk1 x).1
  have hU : ∀ x ∈ rowSupport G, tableLabel G (view (Vector.ofFn x)) ∈ U := by
    intro x hx
    simpa only [view_ofFn] using tableLabel_mem_present G x hx
  have hs := stored_reached_code_bound (labelEncoding basis d) hR hW
    (fun x => tableLabel G (view x)) labelRaw hlab U hU (p.eval N) hlabels len hlen target hrun
  have hn : k ≤ N := by
    have hh := size_le_encoding_length g
    dsimp [N]
    omega
  have hu : U.card ≤ d := presentLabels_card_le G σ hBO
  have ht' : t ≤ 2*(1+d*((N+1)*d)) := ht.trans (by gcongr)
  exact hs.trans (by
    rw [statePolynomial_eval]
    exact stateBound_mono hn hu (Nat.le_refl _) ht')

end ComplexCSP.MaltsevTypeStack
