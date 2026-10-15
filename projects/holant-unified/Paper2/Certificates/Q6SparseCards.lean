import Paper2.Certificates.Q6Arrays

/-! Selected actual sparse-orbit cards. Generated tables and polynomials
are untrusted data, verified by finite reduction and ring proofs below. -/
namespace Paper2.Certificates.Q6

def sparseSpecs : Fin 29 → CardSpec :=
  ![⟨0,1,0,1,![0, 1, 3, 2, 5, 4]⟩, ⟨0,1,0,1,![0, 1, 3, 2, 5, 4]⟩, ⟨0,1,0,1,![0, 1, 2, 3, 4, 5]⟩, ⟨0,1,0,1,![0, 1, 2, 3, 4, 5]⟩, ⟨0,1,3,5,![3, 5, 0, 4, 2, 1]⟩, ⟨0,1,0,2,![0, 2, 1, 4, 3, 5]⟩, ⟨0,1,2,4,![2, 4, 0, 5, 3, 1]⟩, ⟨0,1,3,5,![3, 5, 0, 4, 2, 1]⟩, ⟨0,1,0,1,![0, 1, 2, 4, 3, 5]⟩, ⟨0,2,0,2,![0, 4, 2, 5, 1, 3]⟩, ⟨0,3,0,3,![0, 4, 5, 3, 1, 2]⟩, ⟨0,1,0,2,![0, 2, 1, 4, 3, 5]⟩, ⟨0,1,0,2,![0, 2, 1, 5, 4, 3]⟩, ⟨0,2,0,2,![0, 4, 2, 5, 1, 3]⟩, ⟨0,2,2,3,![2, 0, 3, 4, 5, 1]⟩, ⟨0,2,2,3,![2, 0, 3, 5, 1, 4]⟩, ⟨0,3,0,3,![0, 4, 5, 3, 1, 2]⟩, ⟨0,1,0,1,![0, 1, 2, 3, 4, 5]⟩, ⟨0,1,0,1,![0, 1, 2, 3, 4, 5]⟩, ⟨0,1,0,1,![0, 1, 2, 3, 4, 5]⟩, ⟨0,3,0,3,![0, 1, 2, 3, 4, 5]⟩, ⟨0,1,0,1,![0, 1, 2, 3, 4, 5]⟩, ⟨0,3,0,3,![0, 1, 2, 3, 4, 5]⟩, ⟨0,1,0,1,![0, 1, 4, 5, 3, 2]⟩, ⟨0,1,0,1,![0, 1, 2, 3, 4, 5]⟩, ⟨0,4,0,4,![0, 1, 2, 3, 4, 5]⟩, ⟨0,3,0,3,![0, 1, 2, 3, 4, 5]⟩, ⟨0,1,4,5,![4, 5, 0, 1, 3, 2]⟩, ⟨0,1,0,1,![0, 1, 4, 5, 2, 3]⟩]

def sparsePairTable : Fin 29 → Fin 6 → Finset (ℕ × ℕ) :=
  ![![{(28,19), (44,35), (52,7), (56,11)}, {(14,50), (22,22), (38,38), (26,26), (42,42), (50,14)}, {(14,49), (22,21), (38,37), (26,25), (42,41), (50,13)}, {(13,50), (21,22), (37,38), (25,26), (41,42), (49,14)}, {(13,49), (21,21), (37,37), (25,25), (41,41), (49,13)}, {(7,52), (11,56), (19,28), (35,44)}], ![{(28,19), (44,35), (52,7), (56,11)}, {(14,50), (22,22), (38,38), (26,26), (42,42), (50,14)}, {(14,49), (22,21), (38,37), (26,25), (42,41), (50,13)}, {(13,50), (21,22), (37,38), (25,26), (41,42), (49,14)}, {(13,49), (21,21), (37,37), (25,25), (41,41), (49,13)}, {(7,52), (11,56), (19,28), (35,44)}], ![{(28,35), (44,19), (52,11), (56,7)}, {(14,50), (22,42), (38,26), (26,38), (42,22), (50,14)}, {(14,49), (22,41), (38,25), (26,37), (42,21), (50,13)}, {(13,50), (21,42), (37,26), (25,38), (41,22), (49,14)}, {(13,49), (21,41), (37,25), (25,37), (41,21), (49,13)}, {(7,56), (11,52), (19,44), (35,28)}], ![{(28,35), (44,19), (52,11), (56,7)}, {(14,50), (22,42), (38,26), (26,38), (42,22), (50,14)}, {(14,49), (22,41), (38,25), (26,37), (42,21), (50,13)}, {(13,50), (21,42), (37,26), (25,38), (41,22), (49,14)}, {(13,49), (21,41), (37,25), (25,37), (41,21), (49,13)}, {(7,56), (11,52), (19,44), (35,28)}], ![{(28,42), (44,44), (52,56), (56,41)}, {(14,38), (22,50), (38,52), (26,35), (42,37), (50,49)}, {(14,14), (22,26), (38,28), (26,11), (42,13), (50,25)}, {(13,38), (21,50), (37,52), (25,35), (41,37), (49,49)}, {(13,14), (21,26), (37,28), (25,11), (41,13), (49,25)}, {(7,22), (11,7), (19,19), (35,21)}], ![{(28,37), (44,13), (52,21), (56,7)}, {(14,44), (22,52), (38,28), (26,38), (42,14), (50,22)}, {(14,41), (22,49), (38,25), (26,35), (42,11), (50,19)}, {(13,44), (21,52), (37,28), (25,38), (41,14), (49,22)}, {(13,41), (21,49), (37,25), (25,35), (41,11), (49,19)}, {(7,56), (11,42), (19,50), (35,26)}], ![{(28,22), (44,28), (52,52), (56,21)}, {(14,26), (22,50), (38,56), (26,19), (42,25), (50,49)}, {(14,14), (22,38), (38,44), (26,7), (42,13), (50,37)}, {(13,26), (21,50), (37,56), (25,19), (41,25), (49,49)}, {(13,14), (21,38), (37,44), (25,7), (41,13), (49,37)}, {(7,42), (11,11), (19,35), (35,41)}], ![{(28,42), (44,44), (52,56), (56,41)}, {(14,38), (22,50), (38,52), (26,35), (42,37), (50,49)}, {(14,14), (22,26), (38,28), (26,11), (42,13), (50,25)}, {(13,38), (21,50), (37,52), (25,35), (41,37), (49,49)}, {(13,14), (21,26), (37,28), (25,11), (41,13), (49,25)}, {(7,22), (11,7), (19,19), (35,21)}], ![{(28,35), (44,11), (52,19), (56,7)}, {(14,42), (22,50), (38,26), (26,38), (42,14), (50,22)}, {(14,41), (22,49), (38,25), (26,37), (42,13), (50,21)}, {(13,42), (21,50), (37,26), (25,38), (41,14), (49,22)}, {(13,41), (21,49), (37,25), (25,37), (41,13), (49,21)}, {(7,56), (11,44), (19,52), (35,28)}], ![{(26,13), (42,7), (50,37), (56,21)}, {(14,14), (22,44), (38,38), (28,28), (44,22), (52,52)}, {(14,11), (22,41), (38,35), (28,25), (44,19), (52,49)}, {(11,14), (19,44), (35,38), (25,28), (41,22), (49,52)}, {(11,11), (19,41), (35,35), (25,25), (41,19), (49,49)}, {(7,42), (13,26), (21,56), (37,50)}], ![{(22,13), (38,11), (50,41), (52,25)}, {(14,14), (26,44), (42,42), (28,28), (44,26), (56,56)}, {(14,7), (26,37), (42,35), (28,21), (44,19), (56,49)}, {(7,14), (19,44), (35,42), (21,28), (37,26), (49,56)}, {(7,7), (19,37), (35,35), (21,21), (37,19), (49,49)}, {(11,38), (13,22), (25,52), (41,50)}], ![{(28,37), (44,13), (52,21), (56,7)}, {(14,44), (22,52), (38,28), (26,38), (42,14), (50,22)}, {(14,41), (22,49), (38,25), (26,35), (42,11), (50,19)}, {(13,44), (21,52), (37,28), (25,38), (41,14), (49,22)}, {(13,41), (21,49), (37,25), (25,35), (41,11), (49,19)}, {(7,56), (11,42), (19,50), (35,26)}], ![{(28,13), (44,21), (52,37), (56,7)}, {(14,28), (22,44), (38,52), (26,14), (42,22), (50,38)}, {(14,25), (22,41), (38,49), (26,11), (42,19), (50,35)}, {(13,28), (21,44), (37,52), (25,14), (41,22), (49,38)}, {(13,25), (21,41), (37,49), (25,11), (41,19), (49,35)}, {(7,56), (11,26), (19,42), (35,50)}], ![{(26,13), (42,7), (50,37), (56,21)}, {(14,14), (22,44), (38,38), (28,28), (44,22), (52,52)}, {(14,11), (22,41), (38,35), (28,25), (44,19), (52,49)}, {(11,14), (19,44), (35,38), (25,28), (41,22), (49,52)}, {(11,11), (19,41), (35,35), (25,25), (41,19), (49,49)}, {(7,42), (13,26), (21,56), (37,50)}], ![{(26,14), (42,44), (50,28), (56,13)}, {(14,42), (22,26), (38,56), (28,11), (44,41), (52,25)}, {(14,38), (22,22), (38,52), (28,7), (44,37), (52,21)}, {(11,42), (19,26), (35,56), (25,11), (41,41), (49,25)}, {(11,38), (19,22), (35,52), (25,7), (41,37), (49,21)}, {(7,50), (13,35), (21,19), (37,49)}], ![{(26,28), (42,14), (50,44), (56,13)}, {(14,26), (22,56), (38,42), (28,25), (44,11), (52,41)}, {(14,22), (22,52), (38,38), (28,21), (44,7), (52,37)}, {(11,26), (19,56), (35,42), (25,25), (41,11), (49,41)}, {(11,22), (19,52), (35,38), (25,21), (41,7), (49,37)}, {(7,50), (13,19), (21,49), (37,35)}], ![{(22,13), (38,11), (50,41), (52,25)}, {(14,14), (26,44), (42,42), (28,28), (44,26), (56,56)}, {(14,7), (26,37), (42,35), (28,21), (44,19), (56,49)}, {(7,14), (19,44), (35,42), (21,28), (37,26), (49,56)}, {(7,7), (19,37), (35,35), (21,21), (37,19), (49,49)}, {(11,38), (13,22), (25,52), (41,50)}], ![{(28,35), (44,19), (52,11), (56,7)}, {(14,50), (22,42), (38,26), (26,38), (42,22), (50,14)}, {(14,49), (22,41), (38,25), (26,37), (42,21), (50,13)}, {(13,50), (21,42), (37,26), (25,38), (41,22), (49,14)}, {(13,49), (21,41), (37,25), (25,37), (41,21), (49,13)}, {(7,56), (11,52), (19,44), (35,28)}], ![{(28,35), (44,19), (52,11), (56,7)}, {(14,50), (22,42), (38,26), (26,38), (42,22), (50,14)}, {(14,49), (22,41), (38,25), (26,37), (42,21), (50,13)}, {(13,50), (21,42), (37,26), (25,38), (41,22), (49,14)}, {(13,49), (21,41), (37,25), (25,37), (41,21), (49,13)}, {(7,56), (11,52), (19,44), (35,28)}], ![{(28,35), (44,19), (52,11), (56,7)}, {(14,50), (22,42), (38,26), (26,38), (42,22), (50,14)}, {(14,49), (22,41), (38,25), (26,37), (42,21), (50,13)}, {(13,50), (21,42), (37,26), (25,38), (41,22), (49,14)}, {(13,49), (21,41), (37,25), (25,37), (41,21), (49,13)}, {(7,56), (11,52), (19,44), (35,28)}], ![{(22,41), (38,25), (50,13), (52,11)}, {(14,56), (26,44), (42,28), (28,42), (44,26), (56,14)}, {(14,49), (26,37), (42,21), (28,35), (44,19), (56,7)}, {(7,56), (19,44), (35,28), (21,42), (37,26), (49,14)}, {(7,49), (19,37), (35,21), (21,35), (37,19), (49,7)}, {(11,52), (13,50), (25,38), (41,22)}], ![{(28,35), (44,19), (52,11), (56,7)}, {(14,50), (22,42), (38,26), (26,38), (42,22), (50,14)}, {(14,49), (22,41), (38,25), (26,37), (42,21), (50,13)}, {(13,50), (21,42), (37,26), (25,38), (41,22), (49,14)}, {(13,49), (21,41), (37,25), (25,37), (41,21), (49,13)}, {(7,56), (11,52), (19,44), (35,28)}], ![{(22,41), (38,25), (50,13), (52,11)}, {(14,56), (26,44), (42,28), (28,42), (44,26), (56,14)}, {(14,49), (26,37), (42,21), (28,35), (44,19), (56,7)}, {(7,56), (19,44), (35,28), (21,42), (37,26), (49,14)}, {(7,49), (19,37), (35,21), (21,35), (37,19), (49,7)}, {(11,52), (13,50), (25,38), (41,22)}], ![{(28,7), (44,11), (52,35), (56,19)}, {(14,14), (22,38), (38,42), (26,22), (42,26), (50,50)}, {(14,13), (22,37), (38,41), (26,21), (42,25), (50,49)}, {(13,14), (21,38), (37,42), (25,22), (41,26), (49,50)}, {(13,13), (21,37), (37,41), (25,21), (41,25), (49,49)}, {(7,44), (11,28), (19,52), (35,56)}], ![{(28,35), (44,19), (52,11), (56,7)}, {(14,50), (22,42), (38,26), (26,38), (42,22), (50,14)}, {(14,49), (22,41), (38,25), (26,37), (42,21), (50,13)}, {(13,50), (21,42), (37,26), (25,38), (41,22), (49,14)}, {(13,49), (21,41), (37,25), (25,37), (41,21), (49,13)}, {(7,56), (11,52), (19,44), (35,28)}], ![{(14,49), (38,25), (42,21), (44,19)}, {(22,56), (26,52), (50,28), (28,50), (52,26), (56,22)}, {(22,41), (26,37), (50,13), (28,35), (52,11), (56,7)}, {(7,56), (11,52), (35,28), (13,50), (37,26), (41,22)}, {(7,41), (11,37), (35,13), (13,35), (37,11), (41,7)}, {(19,44), (21,42), (25,38), (49,14)}], ![{(22,41), (38,25), (50,13), (52,11)}, {(14,56), (26,44), (42,28), (28,42), (44,26), (56,14)}, {(14,49), (26,37), (42,21), (28,35), (44,19), (56,7)}, {(7,56), (19,44), (35,28), (21,42), (37,26), (49,14)}, {(7,49), (19,37), (35,21), (21,35), (37,19), (49,7)}, {(11,52), (13,50), (25,38), (41,22)}], ![{(28,52), (44,56), (52,50), (56,49)}, {(14,44), (22,38), (38,42), (26,37), (42,41), (50,35)}, {(14,28), (22,22), (38,26), (26,21), (42,25), (50,19)}, {(13,44), (21,38), (37,42), (25,37), (41,41), (49,35)}, {(13,28), (21,22), (37,26), (25,21), (41,25), (49,19)}, {(7,14), (11,13), (19,7), (35,11)}], ![{(28,11), (44,7), (52,35), (56,19)}, {(14,14), (22,42), (38,38), (26,26), (42,22), (50,50)}, {(14,13), (22,41), (38,37), (26,25), (42,21), (50,49)}, {(13,14), (21,42), (37,38), (25,26), (41,22), (49,50)}, {(13,13), (21,41), (37,37), (25,25), (41,21), (49,49)}, {(7,44), (11,28), (19,56), (35,52)}]]

def sparseCardOrbit : Fin 29 → Fin 24 := ![2, 3, 4, 5, 6, 7, 7, 7, 8, 9, 9, 10, 10, 10, 10, 10, 10, 11, 12, 13, 14, 15, 16, 16, 17, 18, 19, 19, 20]

def sparseFormula {K : Type*} [CommRing K] (u : Fin 8 → K) (t : K) :
    Fin 29 → Fin 6 → K :=
  ![![t, (u 1)^2, -(u 0)*(u 1), -(u 0)*(u 1), (u 0)^2, t], ![t, (u 3)^2, (u 1)*(u 2), (u 1)*(u 2), (u 0)^2, t], ![t, 2*(u 0)^2, -3*(u 0)^2, -3*(u 0)^2, 2*(u 0)^2, t], ![t, 2*(u 1)^2, -3*(u 0)*(u 1), -3*(u 0)*(u 1), 2*(u 0)^2, t], ![t, -(u 2)^2, (u 2)^2, (u 1)^2, -(u 1)^2, t], ![t, (u 4)*(u 5), (u 1)*(u 4), (u 1)*(u 4), (u 0)*(u 1), t], ![t, (u 3)*(u 5), (u 3)^2, (u 2)^2, (u 0)*(u 2), t], ![t, (u 3)*(u 4), (u 3)^2, (u 2)^2, (u 1)*(u 2), t], ![t, 2*(u 3)^2, -2*(u 0)*(u 3), -2*(u 0)*(u 3), 2*(u 0)^2, t], ![t, (u 4)^2, (u 2)*(u 3), (u 2)*(u 3), (u 1)^2, t], ![t, (u 5)^2, -(u 0)*(u 5), -(u 0)*(u 5), (u 0)^2, t], ![t, (u 5)*(u 6), (u 2)*(u 5), (u 2)*(u 5), (u 1)*(u 2), t], ![t, (u 4)*(u 7), (u 3)*(u 4), (u 3)*(u 4), (u 0)*(u 3), t], ![t, (u 5)^2, (u 3)*(u 4), (u 3)*(u 4), (u 2)^2, t], ![t, (u 4)*(u 6), (u 4)^2, (u 3)^2, (u 1)*(u 3), t], ![t, (u 5)*(u 7), (u 5)^2, (u 2)^2, (u 0)*(u 2), t], ![t, (u 7)^2, (u 1)*(u 6), (u 1)*(u 6), (u 0)^2, t], ![-4*(u 0)^2 + t, -2*(u 0)^2, -6*(u 0)^2, -6*(u 0)^2, -2*(u 0)^2, -4*(u 0)^2 + t], ![4*(u 0)^2 + t, -2*(u 0)^2, 6*(u 0)^2, 6*(u 0)^2, -2*(u 0)^2, 4*(u 0)^2 + t], ![-4*(u 0)^2 + t, 2*(u 0)^2, -6*(u 0)^2, -6*(u 0)^2, 2*(u 0)^2, -4*(u 0)^2 + t], ![-3*(u 0)^2 + (u 1)*(u 2) + t, 2*(u 0)^2, -6*(u 0)^2, -6*(u 0)^2, 2*(u 0)^2, -3*(u 0)^2 + (u 1)*(u 2) + t], ![4*(u 0)^2 + t, -2*(u 0)^2, 6*(u 0)^2, 6*(u 0)^2, -2*(u 0)^2, 4*(u 0)^2 + t], ![2*(u 0)^2 - 2*(u 1)*(u 2) + t, -2*(u 0)^2, 6*(u 0)^2, 6*(u 0)^2, -2*(u 0)^2, 2*(u 0)^2 - 2*(u 1)*(u 2) + t], ![t, 3*(u 0)^2 - (u 2)^2, -(u 0)^2 + (u 0)*(u 1) + (u 0)*(u 2) + (u 1)*(u 2), -(u 0)^2 - (u 0)*(u 1) - (u 0)*(u 2) + (u 1)*(u 2), 3*(u 0)^2 - (u 1)^2, t], ![-4*(u 0)^2 + t, 2*(u 0)^2, -6*(u 0)^2, -6*(u 0)^2, 2*(u 0)^2, -4*(u 0)^2 + t], ![-3*(u 0)^2 + (u 1)*(u 2) + t, 2*(u 0)^2, -6*(u 0)^2, -6*(u 0)^2, 2*(u 0)^2, -3*(u 0)^2 + (u 1)*(u 2) + t], ![-2*(u 0)^2 - 2*(u 1)*(u 2) + t, 2*(u 0)^2, -6*(u 0)^2, -6*(u 0)^2, 2*(u 0)^2, -2*(u 0)^2 - 2*(u 1)*(u 2) + t], ![t, (u 0)^2 + (u 0)*(u 1) + (u 0)*(u 2) - (u 2)^2, -(u 0)^2 - (u 0)*(u 1) - (u 0)*(u 2) + (u 2)^2, -(u 0)^2 - (u 0)*(u 1) - (u 0)*(u 2) + (u 1)^2, (u 0)^2 + (u 0)*(u 1) + (u 0)*(u 2) - (u 1)^2, t], ![4*(u 0)^2 + t, 3*(u 0)^2 - 2*(u 0)*(u 3) + (u 4)^2, -3*(u 0)^2 + (u 0)*(u 1) - (u 0)*(u 4) + (u 2)*(u 3), -3*(u 0)^2 + (u 0)*(u 1) - (u 0)*(u 4) + (u 2)*(u 3), 3*(u 0)^2 + 2*(u 0)*(u 2) + (u 1)^2, 4*(u 0)^2 + t]]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sparse_specs_valid (i : Fin 29) : ValidCardSpec (sparseSpecs i) := by
  unfold ValidCardSpec
  revert i
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sparse_pair_table_correct (i : Fin 29) (e : Fin 6) :
    (internalChoices (sparseSpecs i) e).image (sourceMasks (sparseSpecs i) e) =
      sparsePairTable i e := by
  revert i e
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem sparse_source_injective (i : Fin 29) (e : Fin 6) :
    Set.InjOn (sourceMasks (sparseSpecs i) e) (internalChoices (sparseSpecs i) e) := by
  apply Finset.card_image_iff.mp
  revert i e
  decide +kernel

theorem twoCopyArray_eq_sparse_table {K : Type*} [CommRing K]
    (q : Fin 20 → K) (t : K) (i : Fin 29) (e : Fin 6) :
    twoCopyArray q t (sparseSpecs i) e =
      (if e = 0 ∨ e = 5 then t else 0) +
        ∑ ab ∈ sparsePairTable i e, coefficient q ab.1 * coefficient q ab.2 := by
  rw [twoCopyArray, ← sparse_pair_table_correct]
  congr 1
  exact (Finset.sum_image (f := fun ab : ℕ × ℕ =>
    coefficient q ab.1 * coefficient q ab.2) (sparse_source_injective i e)).symm

-- Official orbit 2, deduplicated card 6.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_0 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 0)) t (sparseSpecs 0) = sparseFormula u t 0 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,19), (44,35), (52,7), (56,11)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 0)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 0)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,50), (22,22), (38,38), (26,26), (42,42), (50,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 0)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 0)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 1)) * (0) + ((-(u 1)) * (-(u 1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * ((u 1))))))) = (u 1)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,49), (22,21), (38,37), (26,25), (42,41), (50,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 0)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 0)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 1)) * (-(u 0)) + ((-(u 1)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((u 0)) + (0) * (0)))))) = -(u 0)*(u 1)
    ring
  · change 0 + (∑ ab ∈ ({(13,50), (21,22), (37,38), (25,26), (41,42), (49,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 0)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 0)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + ((0) * (-(u 1)) + ((0) * (0) + ((0) * (0) + (((u 0)) * (0) + (-(u 0)) * ((u 1))))))) = -(u 0)*(u 1)
    ring
  · change 0 + (∑ ab ∈ ({(13,49), (21,21), (37,37), (25,25), (41,41), (49,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 0)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 0)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (-(u 0)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + (((u 0)) * ((u 0)) + (-(u 0)) * (0)))))) = (u 0)^2
    ring
  · change t + (∑ ab ∈ ({(7,52), (11,56), (19,28), (35,44)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 0)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 0)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring

-- Official orbit 3, deduplicated card 6.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_1 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 1)) t (sparseSpecs 1) = sparseFormula u t 1 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,19), (44,35), (52,7), (56,11)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 1)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 1)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,50), (22,22), (38,38), (26,26), (42,42), (50,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 1)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 1)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 2)) * (0) + (((u 3)) * ((u 3)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * ((u 2))))))) = (u 3)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,49), (22,21), (38,37), (26,25), (42,41), (50,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 1)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 1)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 2)) * ((u 1)) + (((u 3)) * (0) + ((0) * (0) + ((0) * (0) + ((0) * ((u 0)) + (0) * (0)))))) = (u 1)*(u 2)
    ring
  · change 0 + (∑ ab ∈ ({(13,50), (21,22), (37,38), (25,26), (41,42), (49,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 1)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 1)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + ((0) * ((u 3)) + ((0) * (0) + ((0) * (0) + (((u 0)) * (0) + ((u 1)) * ((u 2))))))) = (u 1)*(u 2)
    ring
  · change 0 + (∑ ab ∈ ({(13,49), (21,21), (37,37), (25,25), (41,41), (49,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 1)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 1)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 1)) + ((0) * (0) + ((0) * (0) + ((0) * (0) + (((u 0)) * ((u 0)) + ((u 1)) * (0)))))) = (u 0)^2
    ring
  · change t + (∑ ab ∈ ({(7,52), (11,56), (19,28), (35,44)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 1)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 1)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring

-- Official orbit 4, deduplicated card 0.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_2 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 2)) t (sparseSpecs 2) = sparseFormula u t 2 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,35), (44,19), (52,11), (56,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 2)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 2)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,50), (22,42), (38,26), (26,38), (42,22), (50,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 2)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 2)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (0) + ((0) * (0) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + ((0) * (0) + (0) * ((u 0))))))) = 2*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,49), (22,41), (38,25), (26,37), (42,21), (50,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 2)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 2)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + ((0) * (0) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + ((0) * (0) + (0) * (0)))))) = -3*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,50), (21,42), (37,26), (25,38), (41,22), (49,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 2)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 2)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + ((0) * (0) + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + ((0) * (0) + (-(u 0)) * ((u 0))))))) = -3*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,49), (21,41), (37,25), (25,37), (41,21), (49,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 2)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 2)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (-(u 0)) + ((0) * (0) + (((u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + ((0) * (0) + (-(u 0)) * (0)))))) = 2*(u 0)^2
    ring
  · change t + (∑ ab ∈ ({(7,56), (11,52), (19,44), (35,28)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 2)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 2)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring

-- Official orbit 5, deduplicated card 0.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_3 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 3)) t (sparseSpecs 3) = sparseFormula u t 3 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,35), (44,19), (52,11), (56,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 3)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 3)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,50), (22,42), (38,26), (26,38), (42,22), (50,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 3)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 3)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 1)) * (0) + ((0) * (0) + ((-(u 1)) * (-(u 1)) + ((-(u 1)) * (-(u 1)) + ((0) * (0) + (0) * ((u 1))))))) = 2*(u 1)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,49), (22,41), (38,25), (26,37), (42,21), (50,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 3)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 3)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 1)) * (-(u 0)) + ((0) * (0) + ((-(u 1)) * ((u 0)) + ((-(u 1)) * ((u 0)) + ((0) * (0) + (0) * (0)))))) = -3*(u 0)*(u 1)
    ring
  · change 0 + (∑ ab ∈ ({(13,50), (21,42), (37,26), (25,38), (41,22), (49,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 3)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 3)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + ((0) * (0) + (((u 0)) * (-(u 1)) + (((u 0)) * (-(u 1)) + ((0) * (0) + (-(u 0)) * ((u 1))))))) = -3*(u 0)*(u 1)
    ring
  · change 0 + (∑ ab ∈ ({(13,49), (21,41), (37,25), (25,37), (41,21), (49,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 3)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 3)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (-(u 0)) + ((0) * (0) + (((u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + ((0) * (0) + (-(u 0)) * (0)))))) = 2*(u 0)^2
    ring
  · change t + (∑ ab ∈ ({(7,56), (11,52), (19,44), (35,28)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 3)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 3)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring

-- Official orbit 6, deduplicated card 92.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_4 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 4)) t (sparseSpecs 4) = sparseFormula u t 4 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,42), (44,44), (52,56), (56,41)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 4)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 4)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,38), (22,50), (38,52), (26,35), (42,37), (50,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 4)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 4)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 2)) * (-(u 2)) + ((0) * (0) + ((-(u 2)) * (0) + (((u 3)) * (0) + ((0) * ((u 0)) + (0) * (-(u 1))))))) = -(u 2)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,14), (22,26), (38,28), (26,11), (42,13), (50,25)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 4)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 4)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 2)) * ((u 2)) + ((0) * ((u 3)) + ((-(u 2)) * (0) + (((u 3)) * (0) + ((0) * (0) + (0) * ((u 1))))))) = (u 2)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,38), (21,50), (37,52), (25,35), (41,37), (49,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 4)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 4)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (-(u 2)) + ((0) * (0) + (((u 0)) * (0) + (((u 1)) * (0) + ((0) * ((u 0)) + (-(u 1)) * (-(u 1))))))) = (u 1)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,14), (21,26), (37,28), (25,11), (41,13), (49,25)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 4)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 4)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 2)) + ((0) * ((u 3)) + (((u 0)) * (0) + (((u 1)) * (0) + ((0) * (0) + (-(u 1)) * ((u 1))))))) = -(u 1)^2
    ring
  · change t + (∑ ab ∈ ({(7,22), (11,7), (19,19), (35,21)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 4)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 4)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring

-- Official orbit 7, deduplicated card 17.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_5 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 5)) t (sparseSpecs 5) = sparseFormula u t 5 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,37), (44,13), (52,21), (56,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 5)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 5)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * ((u 0)) + ((0) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,44), (22,52), (38,28), (26,38), (42,14), (50,22)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 5)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 5)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 3)) * (0) + ((0) * (0) + (((u 4)) * (0) + (((u 5)) * ((u 4)) + ((0) * ((u 3)) + (0) * (0)))))) = (u 4)*(u 5)
    ring
  · change 0 + (∑ ab ∈ ({(14,41), (22,49), (38,25), (26,35), (42,11), (50,19)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 5)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 5)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 3)) * (0) + ((0) * ((u 2)) + (((u 4)) * ((u 1)) + (((u 5)) * (0) + ((0) * (0) + (0) * (0)))))) = (u 1)*(u 4)
    ring
  · change 0 + (∑ ab ∈ ({(13,44), (21,52), (37,28), (25,38), (41,14), (49,22)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 5)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 5)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + ((0) * (0) + (((u 0)) * (0) + (((u 1)) * ((u 4)) + ((0) * ((u 3)) + ((u 2)) * (0)))))) = (u 1)*(u 4)
    ring
  · change 0 + (∑ ab ∈ ({(13,41), (21,49), (37,25), (25,35), (41,11), (49,19)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 5)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 5)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + ((0) * ((u 2)) + (((u 0)) * ((u 1)) + (((u 1)) * (0) + ((0) * (0) + ((u 2)) * (0)))))) = (u 0)*(u 1)
    ring
  · change t + (∑ ab ∈ ({(7,56), (11,42), (19,50), (35,26)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 5)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 5)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * ((u 5))))) = t
    ring

-- Official orbit 7, deduplicated card 80.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_6 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 6)) t (sparseSpecs 6) = sparseFormula u t 6 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,22), (44,28), (52,52), (56,21)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 6)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 6)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,26), (22,50), (38,56), (26,19), (42,25), (50,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 6)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 6)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 3)) * ((u 5)) + ((0) * (0) + (((u 4)) * (0) + (((u 5)) * (0) + ((0) * ((u 1)) + (0) * ((u 2))))))) = (u 3)*(u 5)
    ring
  · change 0 + (∑ ab ∈ ({(14,14), (22,38), (38,44), (26,7), (42,13), (50,37)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 6)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 6)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 3)) * ((u 3)) + ((0) * ((u 4)) + (((u 4)) * (0) + (((u 5)) * (0) + ((0) * (0) + (0) * ((u 0))))))) = (u 3)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,26), (21,50), (37,56), (25,19), (41,25), (49,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 6)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 6)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 5)) + ((0) * (0) + (((u 0)) * (0) + (((u 1)) * (0) + ((0) * ((u 1)) + ((u 2)) * ((u 2))))))) = (u 2)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,14), (21,38), (37,44), (25,7), (41,13), (49,37)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 6)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 6)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 3)) + ((0) * ((u 4)) + (((u 0)) * (0) + (((u 1)) * (0) + ((0) * (0) + ((u 2)) * ((u 0))))))) = (u 0)*(u 2)
    ring
  · change t + (∑ ab ∈ ({(7,42), (11,11), (19,35), (35,41)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 6)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 6)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring

-- Official orbit 7, deduplicated card 92.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_7 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 7)) t (sparseSpecs 7) = sparseFormula u t 7 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,42), (44,44), (52,56), (56,41)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 7)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 7)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,38), (22,50), (38,52), (26,35), (42,37), (50,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 7)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 7)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 3)) * ((u 4)) + ((0) * (0) + (((u 4)) * (0) + (((u 5)) * (0) + ((0) * ((u 0)) + (0) * ((u 2))))))) = (u 3)*(u 4)
    ring
  · change 0 + (∑ ab ∈ ({(14,14), (22,26), (38,28), (26,11), (42,13), (50,25)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 7)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 7)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 3)) * ((u 3)) + ((0) * ((u 5)) + (((u 4)) * (0) + (((u 5)) * (0) + ((0) * (0) + (0) * ((u 1))))))) = (u 3)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,38), (21,50), (37,52), (25,35), (41,37), (49,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 7)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 7)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 4)) + ((0) * (0) + (((u 0)) * (0) + (((u 1)) * (0) + ((0) * ((u 0)) + ((u 2)) * ((u 2))))))) = (u 2)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,14), (21,26), (37,28), (25,11), (41,13), (49,25)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 7)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 7)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 3)) + ((0) * ((u 5)) + (((u 0)) * (0) + (((u 1)) * (0) + ((0) * (0) + ((u 2)) * ((u 1))))))) = (u 1)*(u 2)
    ring
  · change t + (∑ ab ∈ ({(7,22), (11,7), (19,19), (35,21)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 7)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 7)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring

-- Official orbit 8, deduplicated card 2.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_8 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 8)) t (sparseSpecs 8) = sparseFormula u t 8 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,35), (44,11), (52,19), (56,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 8)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 8)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,42), (22,50), (38,26), (26,38), (42,14), (50,22)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 8)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 8)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (-(u 3)) + (((u 2)) * (0) + (((u 3)) * ((u 3)) + (((u 3)) * ((u 3)) + ((-(u 3)) * (0) + (0) * ((u 2))))))) = 2*(u 3)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,41), (22,49), (38,25), (26,37), (42,13), (50,21)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 8)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 8)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 1)) + (((u 2)) * (0) + (((u 3)) * (-(u 0)) + (((u 3)) * (-(u 0)) + ((-(u 3)) * (0) + (0) * ((u 0))))))) = -2*(u 0)*(u 3)
    ring
  · change 0 + (∑ ab ∈ ({(13,42), (21,50), (37,26), (25,38), (41,14), (49,22)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 8)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 8)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (-(u 3)) + (((u 0)) * (0) + ((-(u 0)) * ((u 3)) + ((-(u 0)) * ((u 3)) + (((u 1)) * (0) + (0) * ((u 2))))))) = -2*(u 0)*(u 3)
    ring
  · change 0 + (∑ ab ∈ ({(13,41), (21,49), (37,25), (25,37), (41,13), (49,21)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 8)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 8)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 1)) + (((u 0)) * (0) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + (((u 1)) * (0) + (0) * ((u 0))))))) = 2*(u 0)^2
    ring
  · change t + (∑ ab ∈ ({(7,56), (11,44), (19,52), (35,28)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 8)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 8)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring

-- Official orbit 9, deduplicated card 208.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_9 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 9)) t (sparseSpecs 9) = sparseFormula u t 9 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(26,13), (42,7), (50,37), (56,21)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 9)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 9)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 5)) * (0) + ((-(u 5)) * (0) + ((0) * (-(u 0)) + (0) * ((u 0))))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,14), (22,44), (38,38), (28,28), (44,22), (52,52)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 9)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 9)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + (((u 3)) * (0) + (((u 4)) * ((u 4)) + ((0) * (0) + ((0) * ((u 3)) + (0) * (0)))))) = (u 4)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,11), (22,41), (38,35), (28,25), (44,19), (52,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 9)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 9)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + (((u 3)) * ((u 2)) + (((u 4)) * (0) + ((0) * ((u 1)) + ((0) * (0) + (0) * (0)))))) = (u 2)*(u 3)
    ring
  · change 0 + (∑ ab ∈ ({(11,14), (19,44), (35,38), (25,28), (41,22), (49,52)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 9)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 9)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + ((0) * (0) + ((0) * ((u 4)) + (((u 1)) * (0) + (((u 2)) * ((u 3)) + (0) * (0)))))) = (u 2)*(u 3)
    ring
  · change 0 + (∑ ab ∈ ({(11,11), (19,41), (35,35), (25,25), (41,19), (49,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 9)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 9)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + ((0) * ((u 2)) + ((0) * (0) + (((u 1)) * ((u 1)) + (((u 2)) * (0) + (0) * (0)))))) = (u 1)^2
    ring
  · change t + (∑ ab ∈ ({(7,42), (13,26), (21,56), (37,50)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 9)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 9)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (-(u 5)) + ((0) * ((u 5)) + (((u 0)) * (0) + (-(u 0)) * (0)))) = t
    ring

-- Official orbit 9, deduplicated card 504.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_10 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 10)) t (sparseSpecs 10) = sparseFormula u t 10 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(22,13), (38,11), (50,41), (52,25)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 10)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 10)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 3)) * (0) + (((u 4)) * (0) + ((0) * ((u 2)) + (0) * ((u 1))))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,14), (26,44), (42,42), (28,28), (44,26), (56,56)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 10)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 10)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + (((u 5)) * (0) + ((-(u 5)) * (-(u 5)) + ((0) * (0) + ((0) * ((u 5)) + (0) * (0)))))) = (u 5)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,7), (26,37), (42,35), (28,21), (44,19), (56,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 10)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 10)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + (((u 5)) * (-(u 0)) + ((-(u 5)) * (0) + ((0) * ((u 0)) + ((0) * (0) + (0) * (0)))))) = -(u 0)*(u 5)
    ring
  · change 0 + (∑ ab ∈ ({(7,14), (19,44), (35,42), (21,28), (37,26), (49,56)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 10)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 10)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + ((0) * (0) + ((0) * (-(u 5)) + (((u 0)) * (0) + ((-(u 0)) * ((u 5)) + (0) * (0)))))) = -(u 0)*(u 5)
    ring
  · change 0 + (∑ ab ∈ ({(7,7), (19,37), (35,35), (21,21), (37,19), (49,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 10)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 10)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + ((0) * (-(u 0)) + ((0) * (0) + (((u 0)) * ((u 0)) + ((-(u 0)) * (0) + (0) * (0)))))) = (u 0)^2
    ring
  · change t + (∑ ab ∈ ({(11,38), (13,22), (25,52), (41,50)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 10)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 10)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * ((u 4)) + ((0) * ((u 3)) + (((u 1)) * (0) + ((u 2)) * (0)))) = t
    ring

-- Official orbit 10, deduplicated card 18.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_11 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 11)) t (sparseSpecs 11) = sparseFormula u t 11 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,37), (44,13), (52,21), (56,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 11)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 11)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * ((u 1)) + ((0) * (0) + ((0) * ((u 0)) + (0) * (0)))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,44), (22,52), (38,28), (26,38), (42,14), (50,22)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 11)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 11)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + (((u 4)) * (0) + (((u 5)) * (0) + (((u 6)) * ((u 5)) + (((u 7)) * (0) + (0) * ((u 4))))))) = (u 5)*(u 6)
    ring
  · change 0 + (∑ ab ∈ ({(14,41), (22,49), (38,25), (26,35), (42,11), (50,19)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 11)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 11)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 3)) + (((u 4)) * (0) + (((u 5)) * ((u 2)) + (((u 6)) * (0) + (((u 7)) * (0) + (0) * (0)))))) = (u 2)*(u 5)
    ring
  · change 0 + (∑ ab ∈ ({(13,44), (21,52), (37,28), (25,38), (41,14), (49,22)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 11)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 11)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + (((u 0)) * (0) + (((u 1)) * (0) + (((u 2)) * ((u 5)) + (((u 3)) * (0) + (0) * ((u 4))))))) = (u 2)*(u 5)
    ring
  · change 0 + (∑ ab ∈ ({(13,41), (21,49), (37,25), (25,35), (41,11), (49,19)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 11)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 11)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 3)) + (((u 0)) * (0) + (((u 1)) * ((u 2)) + (((u 2)) * (0) + (((u 3)) * (0) + (0) * (0)))))) = (u 1)*(u 2)
    ring
  · change t + (∑ ab ∈ ({(7,56), (11,42), (19,50), (35,26)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 11)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 11)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * ((u 7)) + ((0) * (0) + (0) * ((u 6))))) = t
    ring

-- Official orbit 10, deduplicated card 21.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_12 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 12)) t (sparseSpecs 12) = sparseFormula u t 12 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,13), (44,21), (52,37), (56,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 12)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 12)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * ((u 0)) + ((0) * ((u 1)) + (0) * (0)))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,28), (22,44), (38,52), (26,14), (42,22), (50,38)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 12)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 12)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + (((u 4)) * (0) + (((u 5)) * (0) + (((u 6)) * (0) + (((u 7)) * ((u 4)) + (0) * ((u 5))))))) = (u 4)*(u 7)
    ring
  · change 0 + (∑ ab ∈ ({(14,25), (22,41), (38,49), (26,11), (42,19), (50,35)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 12)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 12)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 2)) + (((u 4)) * ((u 3)) + (((u 5)) * (0) + (((u 6)) * (0) + (((u 7)) * (0) + (0) * (0)))))) = (u 3)*(u 4)
    ring
  · change 0 + (∑ ab ∈ ({(13,28), (21,44), (37,52), (25,14), (41,22), (49,38)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 12)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 12)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + (((u 0)) * (0) + (((u 1)) * (0) + (((u 2)) * (0) + (((u 3)) * ((u 4)) + (0) * ((u 5))))))) = (u 3)*(u 4)
    ring
  · change 0 + (∑ ab ∈ ({(13,25), (21,41), (37,49), (25,11), (41,19), (49,35)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 12)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 12)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 2)) + (((u 0)) * ((u 3)) + (((u 1)) * (0) + (((u 2)) * (0) + (((u 3)) * (0) + (0) * (0)))))) = (u 0)*(u 3)
    ring
  · change t + (∑ ab ∈ ({(7,56), (11,26), (19,42), (35,50)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 12)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 12)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * ((u 6)) + ((0) * ((u 7)) + (0) * (0)))) = t
    ring

-- Official orbit 10, deduplicated card 208.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_13 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 13)) t (sparseSpecs 13) = sparseFormula u t 13 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(26,13), (42,7), (50,37), (56,21)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 13)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 13)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 6)) * (0) + (((u 7)) * (0) + ((0) * ((u 1)) + (0) * ((u 0))))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,14), (22,44), (38,38), (28,28), (44,22), (52,52)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 13)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 13)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + (((u 4)) * (0) + (((u 5)) * ((u 5)) + ((0) * (0) + ((0) * ((u 4)) + (0) * (0)))))) = (u 5)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,11), (22,41), (38,35), (28,25), (44,19), (52,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 13)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 13)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + (((u 4)) * ((u 3)) + (((u 5)) * (0) + ((0) * ((u 2)) + ((0) * (0) + (0) * (0)))))) = (u 3)*(u 4)
    ring
  · change 0 + (∑ ab ∈ ({(11,14), (19,44), (35,38), (25,28), (41,22), (49,52)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 13)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 13)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + ((0) * (0) + ((0) * ((u 5)) + (((u 2)) * (0) + (((u 3)) * ((u 4)) + (0) * (0)))))) = (u 3)*(u 4)
    ring
  · change 0 + (∑ ab ∈ ({(11,11), (19,41), (35,35), (25,25), (41,19), (49,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 13)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 13)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + ((0) * ((u 3)) + ((0) * (0) + (((u 2)) * ((u 2)) + (((u 3)) * (0) + (0) * (0)))))) = (u 2)^2
    ring
  · change t + (∑ ab ∈ ({(7,42), (13,26), (21,56), (37,50)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 13)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 13)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * ((u 7)) + ((0) * ((u 6)) + (((u 0)) * (0) + ((u 1)) * (0)))) = t
    ring

-- Official orbit 10, deduplicated card 355.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_14 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 14)) t (sparseSpecs 14) = sparseFormula u t 14 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(26,14), (42,44), (50,28), (56,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 14)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 14)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 6)) * (0) + (((u 7)) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,42), (22,26), (38,56), (28,11), (44,41), (52,25)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 14)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 14)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 7)) + (((u 4)) * ((u 6)) + (((u 5)) * (0) + ((0) * (0) + ((0) * ((u 3)) + (0) * ((u 2))))))) = (u 4)*(u 6)
    ring
  · change 0 + (∑ ab ∈ ({(14,38), (22,22), (38,52), (28,7), (44,37), (52,21)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 14)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 14)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 5)) + (((u 4)) * ((u 4)) + (((u 5)) * (0) + ((0) * (0) + ((0) * ((u 1)) + (0) * ((u 0))))))) = (u 4)^2
    ring
  · change 0 + (∑ ab ∈ ({(11,42), (19,26), (35,56), (25,11), (41,41), (49,25)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 14)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 14)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 7)) + ((0) * ((u 6)) + ((0) * (0) + (((u 2)) * (0) + (((u 3)) * ((u 3)) + (0) * ((u 2))))))) = (u 3)^2
    ring
  · change 0 + (∑ ab ∈ ({(11,38), (19,22), (35,52), (25,7), (41,37), (49,21)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 14)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 14)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 5)) + ((0) * ((u 4)) + ((0) * (0) + (((u 2)) * (0) + (((u 3)) * ((u 1)) + (0) * ((u 0))))))) = (u 1)*(u 3)
    ring
  · change t + (∑ ab ∈ ({(7,50), (13,35), (21,19), (37,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 14)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 14)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + (((u 0)) * (0) + ((u 1)) * (0)))) = t
    ring

-- Official orbit 10, deduplicated card 356.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_15 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 15)) t (sparseSpecs 15) = sparseFormula u t 15 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(26,28), (42,14), (50,44), (56,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 15)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 15)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 6)) * (0) + (((u 7)) * (0) + ((0) * (0) + (0) * (0)))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,26), (22,56), (38,42), (28,25), (44,11), (52,41)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 15)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 15)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 6)) + (((u 4)) * (0) + (((u 5)) * ((u 7)) + ((0) * ((u 2)) + ((0) * (0) + (0) * ((u 3))))))) = (u 5)*(u 7)
    ring
  · change 0 + (∑ ab ∈ ({(14,22), (22,52), (38,38), (28,21), (44,7), (52,37)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 15)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 15)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 4)) + (((u 4)) * (0) + (((u 5)) * ((u 5)) + ((0) * ((u 0)) + ((0) * (0) + (0) * ((u 1))))))) = (u 5)^2
    ring
  · change 0 + (∑ ab ∈ ({(11,26), (19,56), (35,42), (25,25), (41,11), (49,41)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 15)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 15)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 6)) + ((0) * (0) + ((0) * ((u 7)) + (((u 2)) * ((u 2)) + (((u 3)) * (0) + (0) * ((u 3))))))) = (u 2)^2
    ring
  · change 0 + (∑ ab ∈ ({(11,22), (19,52), (35,38), (25,21), (41,7), (49,37)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 15)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 15)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * ((u 4)) + ((0) * (0) + ((0) * ((u 5)) + (((u 2)) * ((u 0)) + (((u 3)) * (0) + (0) * ((u 1))))))) = (u 0)*(u 2)
    ring
  · change t + (∑ ab ∈ ({(7,50), (13,19), (21,49), (37,35)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 15)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 15)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * (0) + ((0) * (0) + (((u 0)) * (0) + ((u 1)) * (0)))) = t
    ring

-- Official orbit 10, deduplicated card 504.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_16 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 16)) t (sparseSpecs 16) = sparseFormula u t 16 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(22,13), (38,11), (50,41), (52,25)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 16)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 16)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 4)) * (0) + (((u 5)) * (0) + ((0) * ((u 3)) + (0) * ((u 2))))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,14), (26,44), (42,42), (28,28), (44,26), (56,56)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 16)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 16)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + (((u 6)) * (0) + (((u 7)) * ((u 7)) + ((0) * (0) + ((0) * ((u 6)) + (0) * (0)))))) = (u 7)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,7), (26,37), (42,35), (28,21), (44,19), (56,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 16)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 16)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + (((u 6)) * ((u 1)) + (((u 7)) * (0) + ((0) * ((u 0)) + ((0) * (0) + (0) * (0)))))) = (u 1)*(u 6)
    ring
  · change 0 + (∑ ab ∈ ({(7,14), (19,44), (35,42), (21,28), (37,26), (49,56)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 16)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 16)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + ((0) * (0) + ((0) * ((u 7)) + (((u 0)) * (0) + (((u 1)) * ((u 6)) + (0) * (0)))))) = (u 1)*(u 6)
    ring
  · change 0 + (∑ ab ∈ ({(7,7), (19,37), (35,35), (21,21), (37,19), (49,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 16)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 16)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((0) * (0) + ((0) * ((u 1)) + ((0) * (0) + (((u 0)) * ((u 0)) + (((u 1)) * (0) + (0) * (0)))))) = (u 0)^2
    ring
  · change t + (∑ ab ∈ ({(11,38), (13,22), (25,52), (41,50)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 16)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 16)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((0) * ((u 5)) + ((0) * ((u 4)) + (((u 2)) * (0) + ((u 3)) * (0)))) = t
    ring

-- Official orbit 11, deduplicated card 0.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_17 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 17)) t (sparseSpecs 17) = sparseFormula u t 17 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,35), (44,19), (52,11), (56,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 17)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 17)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + (-(u 0)) * ((u 0))))) = -4*(u 0)^2 + t
    ring
  · change 0 + (∑ ab ∈ ({(14,50), (22,42), (38,26), (26,38), (42,22), (50,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 17)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 17)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + ((u 0)) * (-(u 0))))))) = -2*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,49), (22,41), (38,25), (26,37), (42,21), (50,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 17)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 17)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + ((u 0)) * (-(u 0))))))) = -6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,50), (21,42), (37,26), (25,38), (41,22), (49,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 17)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 17)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + ((u 0)) * (-(u 0))))))) = -6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,49), (21,41), (37,25), (25,37), (41,21), (49,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 17)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 17)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((u 0)) * (-(u 0))))))) = -2*(u 0)^2
    ring
  · change t + (∑ ab ∈ ({(7,56), (11,52), (19,44), (35,28)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 17)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 17)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + (-(u 0)) * ((u 0))))) = -4*(u 0)^2 + t
    ring

-- Official orbit 12, deduplicated card 0.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_18 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 18)) t (sparseSpecs 18) = sparseFormula u t 18 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,35), (44,19), (52,11), (56,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 18)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 18)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + ((u 0)) * ((u 0))))) = 4*(u 0)^2 + t
    ring
  · change 0 + (∑ ab ∈ ({(14,50), (22,42), (38,26), (26,38), (42,22), (50,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 18)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 18)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + (-(u 0)) * ((u 0))))))) = -2*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,49), (22,41), (38,25), (26,37), (42,21), (50,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 18)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 18)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + (-(u 0)) * (-(u 0))))))) = 6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,50), (21,42), (37,26), (25,38), (41,22), (49,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 18)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 18)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + ((u 0)) * ((u 0))))))) = 6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,49), (21,41), (37,25), (25,37), (41,21), (49,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 18)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 18)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((u 0)) * (-(u 0))))))) = -2*(u 0)^2
    ring
  · change t + (∑ ab ∈ ({(7,56), (11,52), (19,44), (35,28)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 18)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 18)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + (-(u 0)) * (-(u 0))))) = 4*(u 0)^2 + t
    ring

-- Official orbit 13, deduplicated card 0.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_19 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 19)) t (sparseSpecs 19) = sparseFormula u t 19 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,35), (44,19), (52,11), (56,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 19)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 19)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + (-(u 0)) * ((u 0))))) = -4*(u 0)^2 + t
    ring
  · change 0 + (∑ ab ∈ ({(14,50), (22,42), (38,26), (26,38), (42,22), (50,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 19)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 19)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + ((u 0)) * (-(u 0))))))) = 2*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,49), (22,41), (38,25), (26,37), (42,21), (50,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 19)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 19)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + ((u 0)) * (-(u 0))))))) = -6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,50), (21,42), (37,26), (25,38), (41,22), (49,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 19)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 19)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((u 0)) * (-(u 0))))))) = -6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,49), (21,41), (37,25), (25,37), (41,21), (49,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 19)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 19)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((u 0)) * (-(u 0))))))) = 2*(u 0)^2
    ring
  · change t + (∑ ab ∈ ({(7,56), (11,52), (19,44), (35,28)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 19)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 19)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + (-(u 0)) * ((u 0))))) = -4*(u 0)^2 + t
    ring

-- Official orbit 14, deduplicated card 600.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_20 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 20)) t (sparseSpecs 20) = sparseFormula u t 20 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(22,41), (38,25), (50,13), (52,11)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 20)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 20)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 0)) * (-(u 0)) + (((u 2)) * ((u 1)) + (((u 0)) * (-(u 0)) + ((u 0)) * (-(u 0))))) = -3*(u 0)^2 + (u 1)*(u 2) + t
    ring
  · change 0 + (∑ ab ∈ ({(14,56), (26,44), (42,28), (28,42), (44,26), (56,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 20)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 20)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (-(u 0)) * (-(u 0))))))) = 2*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,49), (26,37), (42,21), (28,35), (44,19), (56,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 20)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 20)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + (-(u 0)) * ((u 0))))))) = -6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(7,56), (19,44), (35,28), (21,42), (37,26), (49,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 20)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 20)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + ((u 0)) * (-(u 0))))))) = -6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(7,49), (19,37), (35,21), (21,35), (37,19), (49,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 20)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 20)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + ((u 0)) * ((u 0))))))) = 2*(u 0)^2
    ring
  · change t + (∑ ab ∈ ({(11,52), (13,50), (25,38), (41,22)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 20)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 20)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + (((u 1)) * ((u 2)) + (-(u 0)) * ((u 0))))) = -3*(u 0)^2 + (u 1)*(u 2) + t
    ring

-- Official orbit 15, deduplicated card 0.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_21 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 21)) t (sparseSpecs 21) = sparseFormula u t 21 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,35), (44,19), (52,11), (56,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 21)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 21)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + ((u 0)) * ((u 0))))) = 4*(u 0)^2 + t
    ring
  · change 0 + (∑ ab ∈ ({(14,50), (22,42), (38,26), (26,38), (42,22), (50,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 21)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 21)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + (-(u 0)) * ((u 0))))))) = -2*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,49), (22,41), (38,25), (26,37), (42,21), (50,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 21)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 21)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + (-(u 0)) * (-(u 0))))))) = 6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,50), (21,42), (37,26), (25,38), (41,22), (49,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 21)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 21)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + ((u 0)) * ((u 0))))))) = 6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,49), (21,41), (37,25), (25,37), (41,21), (49,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 21)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 21)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + ((u 0)) * (-(u 0))))))) = -2*(u 0)^2
    ring
  · change t + (∑ ab ∈ ({(7,56), (11,52), (19,44), (35,28)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 21)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 21)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + (-(u 0)) * (-(u 0))))) = 4*(u 0)^2 + t
    ring

-- Official orbit 16, deduplicated card 552.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_22 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 22)) t (sparseSpecs 22) = sparseFormula u t 22 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(22,41), (38,25), (50,13), (52,11)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 22)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 22)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 2)) * (-(u 1)) + ((-(u 2)) * ((u 1)) + ((-(u 0)) * (-(u 0)) + (-(u 0)) * (-(u 0))))) = 2*(u 0)^2 - 2*(u 1)*(u 2) + t
    ring
  · change 0 + (∑ ab ∈ ({(14,56), (26,44), (42,28), (28,42), (44,26), (56,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 22)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 22)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + ((u 0)) * ((u 0))))))) = -2*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,49), (26,37), (42,21), (28,35), (44,19), (56,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 22)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 22)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + ((u 0)) * ((u 0))))))) = 6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(7,56), (19,44), (35,28), (21,42), (37,26), (49,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 22)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 22)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + ((u 0)) * ((u 0))))))) = 6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(7,49), (19,37), (35,21), (21,35), (37,19), (49,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 22)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 22)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + ((u 0)) * ((u 0))))))) = -2*(u 0)^2
    ring
  · change t + (∑ ab ∈ ({(11,52), (13,50), (25,38), (41,22)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 22)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 22)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + (((u 1)) * (-(u 2)) + (-(u 1)) * ((u 2))))) = 2*(u 0)^2 - 2*(u 1)*(u 2) + t
    ring

-- Official orbit 16, deduplicated card 17.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_23 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 23)) t (sparseSpecs 23) = sparseFormula u t 23 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,7), (44,11), (52,35), (56,19)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 23)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 23)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + ((u 0)) * (-(u 0))))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,14), (22,38), (38,42), (26,22), (42,26), (50,50)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 23)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 23)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * ((u 0)) + (((u 2)) * (-(u 2)) + ((-(u 2)) * ((u 0)) + (((u 0)) * ((u 2)) + (((u 0)) * ((u 0)) + (-(u 0)) * (-(u 0))))))) = 3*(u 0)^2 - (u 2)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,13), (22,37), (38,41), (26,21), (42,25), (50,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 23)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 23)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + (((u 2)) * ((u 0)) + ((-(u 2)) * (-(u 1)) + (((u 0)) * ((u 0)) + (((u 0)) * ((u 1)) + (-(u 0)) * ((u 0))))))) = -(u 0)^2 + (u 0)*(u 1) + (u 0)*(u 2) + (u 1)*(u 2)
    ring
  · change 0 + (∑ ab ∈ ({(13,14), (21,38), (37,42), (25,22), (41,26), (49,50)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 23)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 23)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 2)) + (((u 0)) * ((u 0)) + (((u 1)) * ((u 2)) + ((-(u 1)) * ((u 0)) + ((u 0)) * (-(u 0))))))) = -(u 0)^2 - (u 0)*(u 1) - (u 0)*(u 2) + (u 1)*(u 2)
    ring
  · change 0 + (∑ ab ∈ ({(13,13), (21,37), (37,41), (25,21), (41,25), (49,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 23)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 23)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + (((u 0)) * (-(u 1)) + (((u 1)) * ((u 0)) + ((-(u 1)) * ((u 1)) + ((u 0)) * ((u 0))))))) = 3*(u 0)^2 - (u 1)^2
    ring
  · change t + (∑ ab ∈ ({(7,44), (11,28), (19,52), (35,56)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 23)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 23)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + (-(u 0)) * ((u 0))))) = t
    ring

-- Official orbit 17, deduplicated card 0.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_24 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 24)) t (sparseSpecs 24) = sparseFormula u t 24 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,35), (44,19), (52,11), (56,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 24)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 24)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + (-(u 0)) * ((u 0))))) = -4*(u 0)^2 + t
    ring
  · change 0 + (∑ ab ∈ ({(14,50), (22,42), (38,26), (26,38), (42,22), (50,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 24)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 24)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + ((u 0)) * ((u 0))))))) = 2*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,49), (22,41), (38,25), (26,37), (42,21), (50,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 24)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 24)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((u 0)) * (-(u 0))))))) = -6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,50), (21,42), (37,26), (25,38), (41,22), (49,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 24)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 24)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + (-(u 0)) * ((u 0))))))) = -6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,49), (21,41), (37,25), (25,37), (41,21), (49,13)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 24)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 24)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + (-(u 0)) * (-(u 0))))))) = 2*(u 0)^2
    ring
  · change t + (∑ ab ∈ ({(7,56), (11,52), (19,44), (35,28)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 24)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 24)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + ((u 0)) * (-(u 0))))) = -4*(u 0)^2 + t
    ring

-- Official orbit 18, deduplicated card 396.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_25 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 25)) t (sparseSpecs 25) = sparseFormula u t 25 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(14,49), (38,25), (42,21), (44,19)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 25)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 25)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 2)) * ((u 1)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + ((u 0)) * (-(u 0))))) = -3*(u 0)^2 + (u 1)*(u 2) + t
    ring
  · change 0 + (∑ ab ∈ ({(22,56), (26,52), (50,28), (28,50), (52,26), (56,22)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 25)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 25)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + (-(u 0)) * (-(u 0))))))) = 2*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(22,41), (26,37), (50,13), (28,35), (52,11), (56,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 25)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 25)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (-(u 0)) * ((u 0))))))) = -6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(7,56), (11,52), (35,28), (13,50), (37,26), (41,22)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 25)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 25)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + ((u 0)) * (-(u 0))))))) = -6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(7,41), (11,37), (35,13), (13,35), (37,11), (41,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 25)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 25)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((u 0)) * ((u 0))))))) = 2*(u 0)^2
    ring
  · change t + (∑ ab ∈ ({(19,44), (21,42), (25,38), (49,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 25)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 25)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + ((u 1)) * ((u 2))))) = -3*(u 0)^2 + (u 1)*(u 2) + t
    ring

-- Official orbit 19, deduplicated card 552.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_26 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 26)) t (sparseSpecs 26) = sparseFormula u t 26 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(22,41), (38,25), (50,13), (52,11)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 26)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 26)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 2)) * (-(u 1)) + ((-(u 2)) * ((u 1)) + (((u 0)) * (-(u 0)) + ((u 0)) * (-(u 0))))) = -2*(u 0)^2 - 2*(u 1)*(u 2) + t
    ring
  · change 0 + (∑ ab ∈ ({(14,56), (26,44), (42,28), (28,42), (44,26), (56,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 26)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 26)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + (-(u 0)) * ((u 0))))))) = 2*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,49), (26,37), (42,21), (28,35), (44,19), (56,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 26)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 26)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (-(u 0)) * ((u 0))))))) = -6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(7,56), (19,44), (35,28), (21,42), (37,26), (49,14)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 26)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 26)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + (-(u 0)) * ((u 0))))))) = -6*(u 0)^2
    ring
  · change 0 + (∑ ab ∈ ({(7,49), (19,37), (35,21), (21,35), (37,19), (49,7)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 26)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 26)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + (-(u 0)) * ((u 0))))))) = 2*(u 0)^2
    ring
  · change t + (∑ ab ∈ ({(11,52), (13,50), (25,38), (41,22)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 26)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 26)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * ((u 0)) + ((-(u 0)) * ((u 0)) + (((u 1)) * (-(u 2)) + (-(u 1)) * ((u 2))))) = -2*(u 0)^2 - 2*(u 1)*(u 2) + t
    ring

-- Official orbit 19, deduplicated card 241.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_27 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 27)) t (sparseSpecs 27) = sparseFormula u t 27 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,52), (44,56), (52,50), (56,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 27)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 27)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + (-(u 0)) * (-(u 0))))) = t
    ring
  · change 0 + (∑ ab ∈ ({(14,44), (22,38), (38,42), (26,37), (42,41), (50,35)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 27)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 27)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * ((u 0)) + (((u 2)) * (-(u 2)) + ((-(u 2)) * (-(u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 1)) + ((u 0)) * ((u 0))))))) = (u 0)^2 + (u 0)*(u 1) + (u 0)*(u 2) - (u 2)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,28), (22,22), (38,26), (26,21), (42,25), (50,19)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 27)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 27)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + (((u 2)) * ((u 2)) + ((-(u 2)) * ((u 0)) + (((u 0)) * ((u 0)) + ((-(u 0)) * ((u 1)) + ((u 0)) * (-(u 0))))))) = -(u 0)^2 - (u 0)*(u 1) - (u 0)*(u 2) + (u 2)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,44), (21,38), (37,42), (25,37), (41,41), (49,35)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 27)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 27)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 2)) + ((-(u 0)) * (-(u 0)) + (((u 1)) * (-(u 0)) + ((-(u 1)) * (-(u 1)) + (-(u 0)) * ((u 0))))))) = -(u 0)^2 - (u 0)*(u 1) - (u 0)*(u 2) + (u 1)^2
    ring
  · change 0 + (∑ ab ∈ ({(13,28), (21,22), (37,26), (25,21), (41,25), (49,19)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 27)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 27)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 2)) + ((-(u 0)) * ((u 0)) + (((u 1)) * ((u 0)) + ((-(u 1)) * ((u 1)) + (-(u 0)) * (-(u 0))))))) = (u 0)^2 + (u 0)*(u 1) + (u 0)*(u 2) - (u 1)^2
    ring
  · change t + (∑ ab ∈ ({(7,14), (11,13), (19,7), (35,11)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 27)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 27)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * ((u 0)) + ((u 0)) * (-(u 0))))) = t
    ring

-- Official orbit 20, deduplicated card -1.
set_option maxHeartbeats 2000000 in
private theorem sparse_card_28 {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) :
    twoCopyArray (fullOrbit u (sparseCardOrbit 28)) t (sparseSpecs 28) = sparseFormula u t 28 := by
  funext e
  rw [twoCopyArray_eq_sparse_table]
  fin_cases e
  · change t + (∑ ab ∈ ({(28,11), (44,7), (52,35), (56,19)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 28)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 28)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 0)) + (((u 0)) * ((u 0)) + (-(u 0)) * (-(u 0))))) = 4*(u 0)^2 + t
    ring
  · change 0 + (∑ ab ∈ ({(14,14), (22,42), (38,38), (26,26), (42,22), (50,50)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 28)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 28)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * ((u 0)) + (((u 3)) * (-(u 0)) + (((u 4)) * ((u 4)) + (((u 0)) * ((u 0)) + ((-(u 0)) * ((u 3)) + ((u 0)) * ((u 0))))))) = 3*(u 0)^2 - 2*(u 0)*(u 3) + (u 4)^2
    ring
  · change 0 + (∑ ab ∈ ({(14,13), (22,41), (38,37), (26,25), (42,21), (50,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 28)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 28)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + (((u 0)) * (-(u 0)) + (((u 3)) * ((u 2)) + (((u 4)) * (-(u 0)) + (((u 0)) * ((u 1)) + ((-(u 0)) * ((u 0)) + ((u 0)) * (-(u 0))))))) = -3*(u 0)^2 + (u 0)*(u 1) - (u 0)*(u 4) + (u 2)*(u 3)
    ring
  · change 0 + (∑ ab ∈ ({(13,14), (21,42), (37,38), (25,26), (41,22), (49,50)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 28)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 28)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * ((u 0)) + (((u 0)) * (-(u 0)) + ((-(u 0)) * ((u 4)) + (((u 1)) * ((u 0)) + (((u 2)) * ((u 3)) + (-(u 0)) * ((u 0))))))) = -3*(u 0)^2 + (u 0)*(u 1) - (u 0)*(u 4) + (u 2)*(u 3)
    ring
  · change 0 + (∑ ab ∈ ({(13,13), (21,41), (37,37), (25,25), (41,21), (49,49)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 28)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 28)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change 0 + ((-(u 0)) * (-(u 0)) + (((u 0)) * ((u 2)) + ((-(u 0)) * (-(u 0)) + (((u 1)) * ((u 1)) + (((u 2)) * ((u 0)) + (-(u 0)) * (-(u 0))))))) = 3*(u 0)^2 + 2*(u 0)*(u 2) + (u 1)^2
    ring
  · change t + (∑ ab ∈ ({(7,44), (11,28), (19,56), (35,52)} : Finset (ℕ × ℕ)),
      coefficient (fullOrbit u (sparseCardOrbit 28)) ab.1 * coefficient (fullOrbit u (sparseCardOrbit 28)) ab.2) = _
    simp (disch := decide) only [Finset.sum_insert, Finset.sum_singleton]
    change t + (((u 0)) * ((u 0)) + ((-(u 0)) * (-(u 0)) + ((-(u 0)) * (-(u 0)) + ((u 0)) * ((u 0))))) = 4*(u 0)^2 + t
    ring

theorem twoCopyArray_sparse {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) (i : Fin 29) :
    twoCopyArray (fullOrbit u (sparseCardOrbit i)) t (sparseSpecs i) = sparseFormula u t i := by
  fin_cases i
  · exact sparse_card_0 u t
  · exact sparse_card_1 u t
  · exact sparse_card_2 u t
  · exact sparse_card_3 u t
  · exact sparse_card_4 u t
  · exact sparse_card_5 u t
  · exact sparse_card_6 u t
  · exact sparse_card_7 u t
  · exact sparse_card_8 u t
  · exact sparse_card_9 u t
  · exact sparse_card_10 u t
  · exact sparse_card_11 u t
  · exact sparse_card_12 u t
  · exact sparse_card_13 u t
  · exact sparse_card_14 u t
  · exact sparse_card_15 u t
  · exact sparse_card_16 u t
  · exact sparse_card_17 u t
  · exact sparse_card_18 u t
  · exact sparse_card_19 u t
  · exact sparse_card_20 u t
  · exact sparse_card_21 u t
  · exact sparse_card_22 u t
  · exact sparse_card_23 u t
  · exact sparse_card_24 u t
  · exact sparse_card_25 u t
  · exact sparse_card_26 u t
  · exact sparse_card_27 u t
  · exact sparse_card_28 u t

theorem sparse_formula_safe {K : Type*} [CommRing K]
    (u : Fin 8 → K) (t : K) (i : Fin 29)
    (h : AllTwoCopySafe (fullOrbit u (sparseCardOrbit i)) t) :
    NecessarySafe (sparseFormula u t i) := by
  rw [← twoCopyArray_sparse]
  exact h (sparseSpecs i) (sparse_specs_valid i)

end Paper2.Certificates.Q6
