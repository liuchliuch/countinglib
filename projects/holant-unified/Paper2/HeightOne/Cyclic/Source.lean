import Paper2.HeightOne.Cyclic.WeightTwo

/-! Actual cyclic minimum-prime consequences. All analytic matching premises
are discharged from the retained actual root-representative menu. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.Cyclic
noncomputable section
open Tractable ExactInput GroupSplit GroupSplit.MatrixGroup PhaseCards EndpointSelfLoop

lemma three_algebraic_root_phases (N : ℕ) (hN : 3 ≤ N) :
    ∃ s : AlgebraicComplex, s ^ N = 1 ∧ ∃ t : AlgebraicComplex, t ^ N = 1 ∧
      ∃ u : AlgebraicComplex, u ^ N = 1 ∧ s ≠ t ∧ s ≠ u ∧ t ≠ u := by
  classical
  obtain ⟨ζ, hζ⟩ := exists_algebraic_primitiveRoot N (by omega)
  let S := Polynomial.nthRootsFinset N (1 : AlgebraicComplex)
  have hS : 3 ≤ S.card := by rw [hζ.card_nthRootsFinset]; exact hN
  obtain ⟨e⟩ : Nonempty (Fin 3 ↪ S) := Function.Embedding.nonempty_of_card_le (by simpa using hS)
  have hp (i : Fin 3) : (e i).val ^ N = 1 :=
    (Polynomial.mem_nthRootsFinset (by omega : 0 < N) 1).mp (e i).property
  have hne (i j : Fin 3) (hij : i ≠ j) : (e i).val ≠ (e j).val :=
    fun h => hij (e.injective (Subtype.ext h))
  exact ⟨(e 0).val, hp 0, (e 1).val, hp 1, (e 2).val, hp 2,
    hne 0 1 (by decide), hne 0 2 (by decide), hne 1 2 (by decide)⟩

lemma walsh_nonzero {n : ℕ} (f : Signature AlgebraicComplex n) (hf : f ≠ 0) :
    walshCoordinates f ≠ 0 := by
  intro hz
  apply hf
  have he := congrArg (walshBasis.action (n := n)) hz
  rw [← walshBasis_inverse_action, InvertibleKernel.action_symm_action] at he
  simpa [InvertibleKernel.action, Signature.coordinateAction] using he

variable {F : SignatureFamily AlgebraicComplex} {N : ℕ} [NeZero N]

/-- All polynomial root phases are available through actual representatives,
not an analytically adjoined kernel. -/
theorem minimum_root_matching_cards (C : RotationCards F N) (L : Language)
    (heven : ∀ f ∈ L.family, Even f.1) (hsafe : AllBinariesSafe L.family)
    {n : ℕ} (hG : actualClasses L.family = cyclicPhaseClasses N)
    (hmin : LeastPrimeArity L.family n) (f : Signature AlgebraicComplex n)
    (hprocessed : (rotationMenu C).Processed ⟨n, f⟩ L) :
    ∀ a b (hab : a ≠ b), ∀ s : AlgebraicComplex, s ^ N = 1 →
      plusContraction a b hab s (walshCoordinates f) ≠ 0 →
      EqualityMatchingSupport (plusContraction a b hab s (walshCoordinates f)) := by
  intro a b hab s hs hn
  let r : rootsOfUnity N AlgebraicComplex := rootsOfUnity.mkOfPowEq s hs
  exact minimum_plusCard_matching C L heven hsafe hG hmin f hprocessed a b hab r hn

/-- Source higher-cyclic Step 1 for the actual saturated minimum prime. -/
theorem minimum_walsh_origin_nonzero (C : RotationCards F N) (L : Language)
    (hN : 3 ≤ N) (heven : ∀ f ∈ L.family, Even f.1) (hsafe : AllBinariesSafe L.family)
    {n : ℕ} (hn : 5 ≤ n) (hG : actualClasses L.family = cyclicPhaseClasses N)
    (hmin : LeastPrimeArity L.family n) (f : Signature AlgebraicComplex n) (hf : f ≠ 0)
    (hprocessed : (rotationMenu C).Processed ⟨n, f⟩ L) : walshCoordinates f (fun _ => false) ≠ 0 :=
  origin_nonzero_of_matching_cards (walshCoordinates f) (walsh_nonzero f hf) hn
    {s | s ^ N = 1} (three_algebraic_root_phases N hN)
    (minimum_root_matching_cards C L heven hsafe hG hmin f hprocessed)

/-- Source weight-two graph has at most one neighbour per vertex, derived from
literal network cards. -/
theorem minimum_walsh_weightTwo_unique (C : RotationCards F N) (L : Language)
    (hN : 3 ≤ N) (heven : ∀ f ∈ L.family, Even f.1) (hsafe : AllBinariesSafe L.family)
    {n : ℕ} (hn : 5 ≤ n) (hG : actualClasses L.family = cyclicPhaseClasses N)
    (hmin : LeastPrimeArity L.family n) (f : Signature AlgebraicComplex n) (hf : f ≠ 0)
    (hprocessed : (rotationMenu C).Processed ⟨n, f⟩ L)
    (u v w : Fin n) (huv : u ≠ v) (huw : u ≠ w)
    (hv : walshCoordinates f (pairWord u v) ≠ 0) (hw : walshCoordinates f (pairWord u w) ≠ 0) : v = w :=
  weightTwo_unique_partner (walshCoordinates f) (walsh_nonzero f hf) hn
    {s | s ^ N = 1} (three_algebraic_root_phases N hN)
    (minimum_root_matching_cards C L heven hsafe hG hmin f hprocessed) u v w huv huw hv hw

/-- Every supported weight-two edge constrains the entire original Walsh
support, before any block factorization has been assumed. -/
theorem minimum_walsh_weightTwo_equality (C : RotationCards F N) (L : Language)
    (hN : 3 ≤ N) (heven : ∀ f ∈ L.family, Even f.1) (hsafe : AllBinariesSafe L.family)
    {n : ℕ} (hn : 5 ≤ n) (hG : actualClasses L.family = cyclicPhaseClasses N)
    (hmin : LeastPrimeArity L.family n) (f : Signature AlgebraicComplex n) (hf : f ≠ 0)
    (hprocessed : (rotationMenu C).Processed ⟨n, f⟩ L)
    (u v : Fin n) (huv : u ≠ v) (huvF : walshCoordinates f (pairWord u v) ≠ 0) :
    ∀ x, walshCoordinates f x ≠ 0 → x u = x v :=
  weightTwo_forces_equality (walshCoordinates f) (walsh_nonzero f hf) hn
    {s | s ^ N = 1} (three_algebraic_root_phases N hN)
    (minimum_root_matching_cards C L heven hsafe hG hmin f hprocessed) u v huv huvF

end
end Paper2.HeightOne.Cyclic
