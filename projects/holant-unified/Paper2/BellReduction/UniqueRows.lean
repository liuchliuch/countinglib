import Paper2.Complexity.ClosedNetworkSemantics

/-! Positive-arity rows in a well-formed raw graph have unique positions.
This follows from the real incidence permutation, not from a simple-graph or
loopless assumption. Nullary rows are deliberately excluded. -/
namespace Paper2.BellReduction
open Complexity

theorem positive_row_position_unique {G : RawClosedNetwork} {s b : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s b arity) (i j : Fin G.vertices.length)
    (hpos : 0 < arity (G.vertices.get i).1)
    (heq : G.vertices.get i = G.vertices.get j) : i = j := by
  have hpos' : 0 < arity (G.vertices.get j).1 := by simpa only [heq] using hpos
  let p : G.Ports arity := ⟨i,⟨0,hpos⟩⟩
  let q : G.Ports arity := ⟨j,⟨0,hpos'⟩⟩
  have hep : G.portEndpoint hG p = G.portEndpoint hG q := by
    have hi : 0 < (G.vertices.get i).2.length := by rw [(hG.1 i).2]; exact hpos
    have hj : 0 < (G.vertices.get j).2.length := by rw [(hG.1 j).2]; exact hpos'
    have hh := congrArg (fun r : RawVertex => r.2[0]?) heq
    simp only [List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hj,Option.some.injEq] at hh
    exact hh
  have hr : G.route hG p = G.route hG q := by
    apply Prod.ext
    · apply Fin.ext
      exact congrArg (fun e : RawEndpoint => e.1) hep
    · change (G.portEndpoint hG p).2 = (G.portEndpoint hG q).2
      exact congrArg (fun e : RawEndpoint => e.2) hep
  exact congrArg Sigma.fst ((G.route_bijective hG).1 hr)

/-- In particular, separately designated binary occurrences cannot have the
same raw row. Comparing raw rows is safe for deleting selected occurrences. -/
theorem marked_binary_row_unique {G : RawClosedNetwork} {s b : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s b arity) (hzero : arity 0 = 2)
    (i j : Fin G.vertices.length) (hi : (G.vertices.get i).1 = 0)
    (heq : G.vertices.get i = G.vertices.get j) : i = j :=
  positive_row_position_unique hG i j (by rw [hi,hzero]; decide) heq

end Paper2.BellReduction
