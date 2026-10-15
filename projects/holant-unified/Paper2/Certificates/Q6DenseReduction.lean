import Paper2.Certificates.Q6Encoding

/-! Dense-family conclusions for the actual Appendix-A two-copy arrays.
The nine chosen wiring specifications are verified bijections in Q6Cards.
The remaining global obligation is the complete signed-space classification
and the sparse-orbit exclusions, not the dense polynomial implications. -/
namespace Paper2.Certificates.Q6

variable {K : Type*} [CommRing K] [NoZeroDivisors K] [CharZero K]

/-- The concrete identity-03 contraction kills orbit 20's principal component. -/
theorem dense20_from_array (u : Fin 5 → K) (t : K)
    (hs : NecessarySafe (twoCopyArray (denseOrbit u 0) t (denseSpecs 0))) : u 0 = 0 := by
  change NecessarySafe (twoCopyArray (denseOrbit u (cardOrbit 0)) t (denseSpecs 0)) at hs
  rw [twoCopyArray_dense] at hs
  exact orbit20_principal_zero (-2*(u 0)^2+u 1*u 4+u 2*u 3+t) (u 0) hs

/-- Orbit 21 is zero whenever its two actual cards satisfy Q6.6--Q6.7. -/
theorem dense21_from_arrays (u : Fin 5 → K) (t : K) (ht : t ≠ 0)
    (hb : NecessarySafe (twoCopyArray (denseOrbit u 1) t (denseSpecs 1)))
    (ha : NecessarySafe (twoCopyArray (denseOrbit u 1) t (denseSpecs 2))) :
    denseOrbit u 1 = 0 := by
  change NecessarySafe (twoCopyArray (denseOrbit u (cardOrbit 1)) t (denseSpecs 1)) at hb
  change NecessarySafe (twoCopyArray (denseOrbit u (cardOrbit 2)) t (denseSpecs 2)) at ha
  rw [twoCopyArray_dense] at ha hb
  have hz := orbit21_zero t (u 0) (u 1) ht
    (by simpa only [neg_mul] using
      (show NecessarySafe ![t, 2*(u 0)^2, -2*(u 0)^2, -2*(u 0)^2, 2*(u 0)^2, t] from ha))
    (by simpa only [neg_mul] using
      (show NecessarySafe ![t, 2*(u 1)^2, -2*(u 1)^2, -2*(u 1)^2, 2*(u 1)^2, t] from hb))
  funext i
  fin_cases i
  all_goals first | exact hz.1 | exact hz.2 | exact neg_eq_zero.mpr hz.1 | exact neg_eq_zero.mpr hz.2

/-- Orbit 22 is zero whenever its three actual cards satisfy Q6.6--Q6.7. -/
theorem dense22_from_arrays (u : Fin 5 → K) (t : K) (ht : t ≠ 0)
    (hp : NecessarySafe (twoCopyArray (denseOrbit u 2) t (denseSpecs 3)))
    (hs : NecessarySafe (twoCopyArray (denseOrbit u 2) t (denseSpecs 4)))
    (ha : NecessarySafe (twoCopyArray (denseOrbit u 2) t (denseSpecs 5))) :
    denseOrbit u 2 = 0 := by
  change NecessarySafe (twoCopyArray (denseOrbit u (cardOrbit 3)) t (denseSpecs 3)) at hp
  change NecessarySafe (twoCopyArray (denseOrbit u (cardOrbit 4)) t (denseSpecs 4)) at hs
  change NecessarySafe (twoCopyArray (denseOrbit u (cardOrbit 5)) t (denseSpecs 5)) at ha
  rw [twoCopyArray_dense] at hp hs ha
  have hz := orbit22_zero t (u 0) (u 1) (u 2) ht
    (by simpa only [neg_mul] using
      (show NecessarySafe ![t, 2*u 1*u 2, -2*u 1*u 2, -2*u 1*u 2, 2*u 1*u 2, t] from hp))
    (by
      rw [show -((u 1)^2+(u 2)^2) = -(u 1)^2-(u 2)^2 by ring]
      exact hs)
    ha
  funext i
  fin_cases i
  all_goals first | exact hz.1 | exact hz.2.1 | exact hz.2.2 |
    exact neg_eq_zero.mpr hz.1 | exact neg_eq_zero.mpr hz.2.1 | exact neg_eq_zero.mpr hz.2.2

/-- Orbit 23 has support only on one complementary pair, from its three actual
cards. Indices 9 and 10 represent the triples 045 and 123. -/
theorem dense23_from_arrays (u : Fin 5 → K) (t : K) (ht : t ≠ 0)
    (h1 : NecessarySafe (twoCopyArray (denseOrbit u 3) t (denseSpecs 6)))
    (h2 : NecessarySafe (twoCopyArray (denseOrbit u 3) t (denseSpecs 7)))
    (h3 : NecessarySafe (twoCopyArray (denseOrbit u 3) t (denseSpecs 8))) :
    ∀ i : Fin 20, denseOrbit u 3 i ≠ 0 → i = 9 ∨ i = 10 := by
  change NecessarySafe (twoCopyArray (denseOrbit u (cardOrbit 6)) t (denseSpecs 6)) at h1
  change NecessarySafe (twoCopyArray (denseOrbit u (cardOrbit 7)) t (denseSpecs 7)) at h2
  change NecessarySafe (twoCopyArray (denseOrbit u (cardOrbit 8)) t (denseSpecs 8)) at h3
  rw [twoCopyArray_dense] at h1 h2 h3
  have hz := orbit23_reduction t (u 0) (u 1) (u 2) (u 3) ht h1 h2 h3
  intro i
  fin_cases i
  all_goals intro hi
  all_goals first | exact False.elim (hi hz.1) | exact False.elim (hi hz.2) |
    exact False.elim (hi (neg_eq_zero.mpr hz.1)) | exact False.elim (hi (neg_eq_zero.mpr hz.2)) |
    exact Or.inl rfl | exact Or.inr rfl

theorem dense23_pair_complementary :
    tripleMasks 9 = 49 ∧ tripleMasks 10 = 14 ∧ Nat.xor (tripleMasks 9) 63 = tripleMasks 10 := by
  decide +kernel

end Paper2.Certificates.Q6
