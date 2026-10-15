import Paper2.Certificates.Q6CoverageCompact

namespace Paper2.Certificates.Q6.Coverage

/-- Every actual coefficient vector satisfying the fifteen complementary-zero
loop conditions lies in an explicitly transported official parameter row.
The compact storage has its own complete kernel-checked DAG and terminal deck. -/
theorem exhaustive_cover {K : Type*} [CommRing K] [NoZeroDivisors K] [CharZero K]
    (q : Fin 20 → K) (h : ∀ d : Fin 15, ∃ b : Fin 3, (loopOptions d b).Holds q) :
    InOrbits officialRows q := compact_exhaustive_cover q h

end Paper2.Certificates.Q6.Coverage
