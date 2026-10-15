import Paper2.HeightOne.PhaseCards.Cards
import Paper2.HeightOne.PhaseCards.PrimeParity
import Paper2.HeightOne.PhaseCards.BinaryParity

/-! Paper 2 Lemma 5.10: actual chosen binary cards, ordered distinct ports,
actual tensor-prime factorizations, and the exact scalar-2 Walsh bridge. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable GroupSplit GroupSplit.MatrixGroup EndpointSelfLoop
variable {ι : Type} [Fintype ι]

lemma walsh_zero : walshCoordinates (0 : Tensor AlgebraicComplex ι) = 0 := by
  funext x
  simp [walshCoordinates, action]

/-- High-arity parity conclusion from prime-factor parity of the genuinely
constructed rotation cards. Zero contractions are explicitly permitted. -/
theorem parity_from_actual_prime_cards {F : SignatureFamily AlgebraicComplex}
    {N : ℕ} (hN : 3 ≤ N) (C : RotationCards F N)
    (hcard : 4 ≤ Fintype.card ι) (f : Tensor AlgebraicComplex ι)
    (h : ∀ (a b : ι) (hab : a ≠ b) (s : rootsOfUnity N AlgebraicComplex),
      C.contraction a b hab s f ≠ 0 →
      PrimeFactorsHaveParity (C.contraction a b hab s f)) :
    HasParity (walshCoordinates f) := by
  letI : NeZero N := ⟨by omega⟩
  obtain ⟨ζ, hζ⟩ := exists_algebraic_primitiveRoot N (by omega)
  apply hasParity_of_root_of_unity_contractions hcard N hN ζ hζ (walshCoordinates f)
  intro a b hab s hs
  let r : rootsOfUnity N AlgebraicComplex := rootsOfUnity.mkOfPowEq s hs
  have hc : HasParity (walshCoordinates (C.contraction a b hab r f)) := by
    by_cases hz : C.contraction a b hab r f = 0
    · rw [hz, walsh_zero]
      exact hasParity_zero
    · apply hasParity_of_primeFactors _ ?_ hz (h a b hab r hz)
      have := remaining_card a b hab
      omega
  rw [C.walsh] at hc
  exact (hasParity_scale_iff _ (C.walsh_scale_ne_zero r) _).mp hc

/-- Cyclic strengthening. Positive prime factors of nonzero actual cards are
even; their nullary normalization scalars impose no hypothesis. -/
theorem even_from_actual_prime_cards {F : SignatureFamily AlgebraicComplex}
    {N : ℕ} (hN : 3 ≤ N) (C : RotationCards F N)
    (hcard : 4 ≤ Fintype.card ι) (f : Tensor AlgebraicComplex ι)
    (h : ∀ (a b : ι) (hab : a ≠ b) (s : rootsOfUnity N AlgebraicComplex),
      C.contraction a b hab s f ≠ 0 → PrimeFactorsEven (C.contraction a b hab s f)) :
    SupportedOnParity (walshCoordinates f) 0 := by
  letI : NeZero N := ⟨by omega⟩
  obtain ⟨ζ, hζ⟩ := exists_algebraic_primitiveRoot N (by omega)
  apply even_of_root_of_unity_contractions (by omega) N (by omega) ζ hζ (walshCoordinates f)
  intro a b hab s hs
  let r : rootsOfUnity N AlgebraicComplex := rootsOfUnity.mkOfPowEq s hs
  have hc : SupportedOnParity (walshCoordinates (C.contraction a b hab r f)) 0 := by
    by_cases hz : C.contraction a b hab r f = 0
    · rw [hz, walsh_zero]
      intro x hx
      exact False.elim (hx rfl)
    · apply even_of_primeFactors _ ?_ hz (h a b hab r hz)
      have := remaining_card a b hab
      omega
  rw [C.walsh] at hc
  exact (supportedOnParity_scale_iff _ (C.walsh_scale_ne_zero r) _ 0).mp hc

/-- The unique ordered 2×2 table of a binary signature. -/
def tableBinary (f : Signature AlgebraicComplex 2) : AMat := fun a b => f ![a, b]

lemma binarySignature_tableBinary (f : Signature AlgebraicComplex 2) :
    binarySignature (tableBinary f) = f := by
  funext x
  apply congrArg f
  funext i
  fin_cases i <;> rfl

lemma actual_tableBinary {F : SignatureFamily AlgebraicComplex}
    (hsafe : AllBinariesSafe F) (f : Signature AlgebraicComplex 2)
    (hf : NetworkRealizable F f) (hn : f ≠ 0) : ActualNonsingular F (tableBinary f) := by
  have hr : NetworkRealizable F (binarySignature (tableBinary f)) := by
    rwa [binarySignature_tableBinary]
  have hz : tableBinary f ≠ 0 := by
    intro h
    apply hn
    rw [← binarySignature_tableBinary f, h]
    rfl
  exact ⟨hr, (hsafe _ hr hz).1⟩

/-- Source Lemma 5.10 in the actual normalized-network setting. The fixed
representatives are supplied by `rotationCards_nonempty`; at arity two complete
group membership gives parity, and at larger arity actual prime cards do. -/
theorem walsh_parity_from_contractions {F : SignatureFamily AlgebraicComplex}
    {N n : ℕ} (hN : 3 ≤ N)
    (hG : actualClasses F = cyclicPhaseClasses N ∨
      actualClasses F = dihedralPhaseClasses N)
    (hsafe : AllBinariesSafe F) (C : RotationCards F N)
    (f : Signature AlgebraicComplex n) (hpos : 0 < n) (heven : Even n)
    (hf : NetworkRealizable F f) (hn : f ≠ 0)
    (h : 4 ≤ n → ∀ (a b : Fin n) (hab : a ≠ b) (s : rootsOfUnity N AlgebraicComplex),
      C.contraction a b hab s f ≠ 0 → PrimeFactorsHaveParity (C.contraction a b hab s f)) :
    HasParity (walshCoordinates f) := by
  by_cases htwo : n = 2
  · subst n
    have hp := normalized_binary_hasParity hG (actual_tableBinary hsafe f hf hn)
    rwa [binarySignature_tableBinary] at hp
  · have hn4 : 4 ≤ n := by obtain ⟨k, hk⟩ := heven; omega
    exact parity_from_actual_prime_cards hN C (by simpa using hn4) f (h hn4)

/-- The same actual theorem with the source's even-parity cyclic conclusion. -/
theorem cyclic_walsh_even_from_contractions {F : SignatureFamily AlgebraicComplex}
    {N n : ℕ} (hN : 3 ≤ N) (hG : actualClasses F = cyclicPhaseClasses N)
    (hsafe : AllBinariesSafe F) (C : RotationCards F N)
    (f : Signature AlgebraicComplex n) (hpos : 0 < n) (heven : Even n)
    (hf : NetworkRealizable F f) (hn : f ≠ 0)
    (h : 4 ≤ n → ∀ (a b : Fin n) (hab : a ≠ b) (s : rootsOfUnity N AlgebraicComplex),
      C.contraction a b hab s f ≠ 0 → PrimeFactorsEven (C.contraction a b hab s f)) :
    SupportedOnParity (walshCoordinates f) 0 := by
  by_cases htwo : n = 2
  · subst n
    have hp := cyclic_binary_even hG (actual_tableBinary hsafe f hf hn)
    rwa [binarySignature_tableBinary] at hp
  · have hn4 : 4 ≤ n := by obtain ⟨k, hk⟩ := heven; omega
    exact even_from_actual_prime_cards hN C (by simpa using hn4) f (h hn4)

end
end Paper2.HeightOne.PhaseCards
