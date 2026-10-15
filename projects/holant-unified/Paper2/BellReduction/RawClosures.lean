import Paper2.BellReduction.RawPairing
import Paper2.BellReduction.MarkedLanguage
import Paper2.BellReduction.RawBellIdentities

/-! Each raw reconnection is followed by two exact native-edge eliminations.
Both closed-circle bits are retained; their factors belong to the arithmetic
postprocessor rather than being discarded from the original graph. -/
namespace Paper2.BellReduction.RawClosures
open Complexity ExactInput Tractable Problem RawOccurrence NativeSmoothing
open NativeSmoothing.Surgery RawNative Bell

structure Result where
  query : RawClosedNetwork
  firstCircle : Bool
  secondCircle : Bool
  deriving DecidableEq

def close (mode : Fin 3) (G : RawClosedNetwork) : Result :=
  let a := Smoothing.compile 0 (RawPairing.query mode G)
  let b := Smoothing.compile 0 a.query
  ⟨b.query,a.circle,b.circle⟩

def scalar {K : Type} [OfNat K 1] [OfNat K 2] [Mul K] (r : Result) : K :=
  (if r.firstCircle then 2 else 1) * (if r.secondCircle then 2 else 1)

 theorem query_count {G : RawClosedNetwork} {s b : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s b arity) (hzero : arity 0 = 2)
    (hc : 2 ≤ markedCount G.vertices) (mode : Fin 3) :
    markedCount (RawPairing.query mode G).vertices = markedCount G.vertices := by
  obtain ⟨p,q,r,t,tail,hp,hp0,hp1,hq0,hq1,hr⟩ := RawPairing.selected_two hG hzero hc
  rw [markedCount_perm hp]
  simp only [RawPairing.query,hp0,hp1,hq0,hq1,hr]
  unfold RawPairing.rows
  split <;> (try split) <;> simp [markedCount]

 theorem close_wellFormed {G : RawClosedNetwork} {s b : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s b arity) (hzero : arity 0 = 2)
    (hc : 2 ≤ markedCount G.vertices) (mode : Fin 3) :
    (close mode G).query.WellFormed s b arity :=
  compile_wellFormed _ (compile_wellFormed _
    (RawPairing.query_wellFormed hG hzero hc mode) 0 hzero) 0 hzero

 theorem close_count {G : RawClosedNetwork} {s b : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s b arity) (hzero : arity 0 = 2)
    (hc : 2 ≤ markedCount G.vertices) (mode : Fin 3) :
    markedCount (close mode G).query.vertices = markedCount G.vertices - 2 := by
  have hw := RawPairing.query_wellFormed hG hzero hc mode
  have h1 := compile_count _ hw 0 hzero
  have h2 := compile_count _ (compile_wellFormed _ hw 0 hzero) 0 hzero
  have h3 := query_count hG hzero hc mode
  change markedCount (Smoothing.compile 0 (RawPairing.query mode G)).query.vertices =
    markedCount (RawPairing.query mode G).vertices - 1 at h1
  change markedCount (close mode G).query.vertices =
    markedCount (Smoothing.compile 0 (RawPairing.query mode G)).query.vertices - 1 at h2
  omega

/-- Weighted query correctness before discarding the absent designated label. -/
theorem close_value {K : Type} [CommSemiring K] (T : Choice.Table K)
    {G : RawClosedNetwork} {s b : ℕ} {arity : ℕ → ℕ}
    (hG : G.WellFormed s b arity) (hzero : arity 0 = 2)
    (hc : 2 ≤ markedCount G.vertices) (mode : Fin 3)
    (hT : ∀ a b, T 0 [a,b] = Signature.disequality a b) :
    evaluate T (RawPairing.query mode G) = scalar (close mode G) * evaluate T (close mode G).query := by
  have hw := RawPairing.query_wellFormed hG hzero hc mode
  have h1 := compile_value T _ hw 0 hzero hT
  have h2 := compile_value T _ (compile_wellFormed _ hw 0 hzero) 0 hzero hT
  rw [h1,h2]
  exact (mul_assoc _ _ _).symm

noncomputable def query (L : Language) (g : Signature AlgebraicComplex 2)
    (G : Instance (RelativeEO.tagged L g)) (hc : markedCount G.val.vertices = 2)
    (mode : Fin 3) : Instance L :=
  ⟨unmark (close mode G.val).query,unmark_wellFormed L g
    ⟨_,close_wellFormed G.property (RelativeEO.tagged_arity_zero L g) (by omega) mode⟩
    (by rw [close_count G.property (RelativeEO.tagged_arity_zero L g) (by omega) mode,hc])⟩

end Paper2.BellReduction.RawClosures
