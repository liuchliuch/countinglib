import Paper2.SourceFaithful.SourceStatements.AppendixPlaneIncidence
import Paper2.SourceFaithful.SourceStatements.AppendixNonplaneGraph
import Mathlib.Basic.Complex.Basic

/-! Literal Proposition A.10 and Theorem A.11. Words index the actual
four-subsets of the eight binary-labelled ports. The unordered pair convention
is represented by symmetry of lambda, with nonzero values on distinct ports.
All coefficients, exact cardinalities, and both source graphs are included.
The graph proofs use checked finite incidence witnesses, rather than an
assertion that an external support-verification script succeeded. -/
namespace Paper2.SourceFaithful.SourceStatements.AppendixSupport
open Paper2.ReedMuller Paper2.Certificates.Q8
noncomputable section

instance nonplaneFintype : Fintype AppendixNonplaneGraph.Nonplane := by
  unfold AppendixNonplaneGraph.Nonplane
  infer_instance

/-- The exact coefficient and support conclusion of source Theorem A.11. -/
theorem source_A_11 (c : Word → ℂ) (lam : Fin 8 → Fin 8 → ℂ)
    (hs : SwapSystem c lam) (hsym : ∀ p q,lam p q=lam q p)
    (hnz : ∀ p q,p≠q→lam p q≠0) :
    ∃ k : ℂ,k≠0 ∧
      (∀ x : Word,weight x=4→
        c x=if supportXor x=(fun _=>false) then k else 0) ∧
      (∀ x : Word,weight x=4→(c x≠0↔IsCentral x)) ∧
      Fintype.card Plane=14 := by
  obtain ⟨k,hk,hc⟩ := canonical_support c lam hs hsym hnz
  refine ⟨k,hk,hc,?_,plane_count⟩
  intro x hw
  rw [hc x hw,central_iff_plane]
  by_cases hx : supportXor x=(fun _=>false) <;> simp [hw,hx,hk]

/-- The complete literal source Proposition A.10: the fourteen supported
planes have one common nonzero coefficient; the fifty-six nonplanes form a
connected exchange graph with an odd cycle; and the exact plane--unordered
port-pair incidence graph is connected. -/
theorem source_A_10 (c : Word → ℂ) (lam : Fin 8 → Fin 8 → ℂ)
    (hs : SwapSystem c lam) (hsym : ∀ p q,lam p q=lam q p)
    (hnz : ∀ p q,p≠q→lam p q≠0) :
    (∃ k : ℂ,k≠0 ∧
      (∀ x : Word,weight x=4→
        c x=if supportXor x=(fun _=>false) then k else 0) ∧
      (∀ x : Word,weight x=4→(c x≠0↔IsCentral x))) ∧
    Fintype.card Plane=14 ∧
    Fintype.card AppendixNonplaneGraph.Nonplane=56 ∧
    AppendixNonplaneGraph.G.Connected ∧
    (∃ v : AppendixNonplaneGraph.Nonplane,
      ∃ w : AppendixNonplaneGraph.G.Walk v v,w.IsCycle ∧ Odd w.length) ∧
    H.Connected := by
  obtain ⟨k,hk,hc,hsupport,hcount⟩ := source_A_11 c lam hs hsym hnz
  obtain ⟨v,w,hcycle,hlen⟩ := AppendixNonplaneGraph.exists_triangle_cycle
  refine ⟨⟨k,hk,hc,hsupport⟩,hcount,nonplane_count,
    AppendixNonplaneGraph.connected,⟨v,w,hcycle,?_⟩,incidence_connected⟩
  rw [hlen]
  decide

end
end Paper2.SourceFaithful.SourceStatements.AppendixSupport

