import Paper2.BellReduction.IterationBounds
import Paper2.BellReduction.EncodedSize
import Paper2.Complexity.BellMachines.BoundedIterateInterface

/-! A polynomial bound on every actual encoded intermediate graph, suitable
for the proved finite bounded-iteration controller. -/
namespace Paper2.BellReduction
open Complexity ExactInput Problem BellMachines RawTriple
open FixedFieldMachines GraphPreprocessing

noncomputable def languageArityBound (L : Language) : ℕ :=
  Finset.univ.sup (fun i : Fin L.count => L.arity i.val)

theorem arity_le_bound (L : Language) (i : ℕ) (hi : i < L.count) :
    L.arity i ≤ languageArityBound L :=
  Finset.le_sup (f := fun i : Fin L.count => L.arity i.val) (Finset.mem_univ ⟨i,hi⟩)

noncomputable def intermediatePolynomial (L : Language) : Polynomial ℕ :=
  Polynomial.C (8*L.count+56*languageArityBound L+16) * Polynomial.X^2

/-- Bound all rounds by the original framed (unary-count, graph) input length.
The proof uses actual counts and actual byte lengths at each round, rather than
iterating the one-step time polynomial exponentially many times. -/
theorem intermediateBound (L : Language) (hzero : L.arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8) :
    BoundedIterate.IntermediateBound (inputEncoding L) (guardedValid L hzero coreLabel hl ha)
      (intermediatePolynomial L) := by
  intro n G k hk
  let H := ((guardedValid L hzero coreLabel hl ha)^[k]) G
  let N := ((BoundedIterate.inputEncoding (inputEncoding L)).encode (n,G)).length
  have hn : N = 2*n+1+((inputEncoding L).encode G).length := by
    simp [N,BoundedIterate.inputEncoding,pairEncoding,UnaryBinary.unaryEncoding]
  have hs := iterate_stats G.property hzero coreLabel hl ha k
  have hV : H.val.vertices.length ≤ G.val.vertices.length := by
    dsimp [H]
    rw [guardedValid_iterate_raw]
    exact hs.2.1
  have hE : H.val.edges.length ≤ G.val.edges.length+2*k := by
    dsimp [H]
    rw [guardedValid_iterate_raw]
    exact hs.2.2.1
  have hinput := counts_le_input_length L G
  have htotal : H.val.vertices.length+H.val.edges.length+1 ≤ N := by omega
  have hbits := raw_encoding_length_bound H.val L.count (languageArityBound L) L.arity
    H.property (arity_le_bound L)
  change (RawClosedNetwork.encoding.encode H.val).length ≤ (intermediatePolynomial L).eval N
  calc
    _ ≤ (8*L.count+56*languageArityBound L+16) *
        (H.val.vertices.length+H.val.edges.length+1)^2 := hbits
    _ ≤ (8*L.count+56*languageArityBound L+16)*N^2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left htotal 2)
    _ = _ := by simp [intermediatePolynomial]

/-- An actual finite Boolean-stack machine performs every requested number of
guarded rounds in polynomial time in the unchanged encoded count and graph. -/
noncomputable def iterateComputes (L : Language) (hzero : L.arity 0 = 2)
    (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8) :
    BinaryCompose.Computes (BoundedIterate.inputEncoding (inputEncoding L)) (inputEncoding L)
      (fun p => ((guardedValid L hzero coreLabel hl ha)^[p.1]) p.2) :=
  BoundedIterate.computes (inputEncoding L) _ (guardedValidComputes L hzero coreLabel hl ha)
    (intermediatePolynomial L) (intermediateBound L hzero coreLabel hl ha)

end Paper2.BellReduction
