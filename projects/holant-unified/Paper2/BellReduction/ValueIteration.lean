import Paper2.BellReduction.ValueSurgery
import Paper2.BellReduction.IterationBounds

/-! Scalar bookkeeping through the actual guarded finite-machine rounds.
The exponent is computed from the original designated occurrence count. -/
namespace Paper2.BellReduction
open Complexity ExactInput Tractable Problem Bell ReedMuller
open RawOccurrence BellMachines.RawTriple

noncomputable def roundsRemaining {L : Language} (G : Instance L) : ℕ :=
  (markedCount G.val.vertices - 1) / 2

variable (L : Language) (hzero : L.arity 0 = 2)
  (coreLabel : ℕ) (hl : coreLabel < L.count) (ha : L.arity coreLabel = 8)
  (c : AlgebraicComplex) (d l : Bool) (hL0 : 0 < L.count)
  (hbell : (⟨L.arity 0,L.signature ⟨0,hL0⟩⟩ : AnySignature AlgebraicComplex) =
    ⟨2,bellTable d l⟩)
  (hcore : (⟨L.arity coreLabel,L.signature ⟨coreLabel,hl⟩⟩ : AnySignature AlgebraicComplex) =
    ⟨8,fun x => c * core x⟩)

include hbell hcore

theorem weighted_guarded_value (G : Instance L) :
    (c * sign l)^roundsRemaining (guardedValid L hzero coreLabel hl ha G) *
      value .nativeX L (guardedValid L hzero coreLabel hl ha G) =
        (c * sign l)^roundsRemaining G * value .nativeX L G := by
  by_cases hc : 3 ≤ markedCount G.val.vertices
  · have he : guardedValid L hzero coreLabel hl ha G =
        transformValid L hzero coreLabel hl ha ⟨G,hc⟩ := by
      apply Subtype.ext
      simp [guardedValid,guarded,hasThree,hc,transformValid]
    rw [he]
    have hcount := valid_count L hzero coreLabel hl ha ⟨G,hc⟩
    change markedCount (transformValid L hzero coreLabel hl ha ⟨G,hc⟩).val.vertices + 2 =
      markedCount G.val.vertices at hcount
    have hr : roundsRemaining G =
        roundsRemaining (transformValid L hzero coreLabel hl ha ⟨G,hc⟩) + 1 := by
      unfold roundsRemaining
      omega
    rw [value_transformValid L hzero coreLabel hl ha c d l hL0 hbell hcore,hr,pow_succ]
    ring
  · have he : guardedValid L hzero coreLabel hl ha G = G := by
      apply Subtype.ext
      simp [guardedValid,guarded,hasThree,hc]
    rw [he]

/-- The same invariant holds after every actual guarded iteration, including
extra no-op rounds once the marked count has dropped to at most two. -/
theorem weighted_iterate_value (G : Instance L) (k : ℕ) :
    (c * sign l)^roundsRemaining (((guardedValid L hzero coreLabel hl ha)^[k]) G) *
      value .nativeX L (((guardedValid L hzero coreLabel hl ha)^[k]) G) =
        (c * sign l)^roundsRemaining G * value .nativeX L G := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    exact (weighted_guarded_value L hzero coreLabel hl ha c d l hL0 hbell hcore _).trans ih

/-- Linear many rounds leave at most two occurrences and multiply the original
answer by precisely the explicitly computed power, with no discarded signs. -/
theorem normalized_value (G : Instance L) :
    value .nativeX L
        (((guardedValid L hzero coreLabel hl ha)^[G.val.vertices.length]) G) =
      (c * sign l)^roundsRemaining G * value .nativeX L G := by
  have hc := iterate_at_most_two G.property hzero coreLabel hl ha
  have hr : roundsRemaining
      (((guardedValid L hzero coreLabel hl ha)^[G.val.vertices.length]) G) = 0 := by
    unfold roundsRemaining
    rw [guardedValid_iterate_raw]
    omega
  have hv := weighted_iterate_value L hzero coreLabel hl ha c d l hL0 hbell hcore G
    G.val.vertices.length
  simpa only [hr,pow_zero,one_mul] using hv

/-- The eventual postprocessor divides only by a fixed nonzero base raised to
a bounded input count. The literal division is separate from its machine proof. -/
theorem original_value_from_normalized (hc : c ≠ 0) (G : Instance L) :
    value .nativeX L G =
      value .nativeX L
        (((guardedValid L hzero coreLabel hl ha)^[G.val.vertices.length]) G) /
          (c * sign l)^roundsRemaining G := by
  have hs : c * sign l ≠ 0 := occurrenceGraph_scalar_ne_zero hc l
  apply (eq_div_iff (pow_ne_zero _ hs)).mpr
  rw [normalized_value L hzero coreLabel hl ha c d l hL0 hbell hcore]
  ring

end Paper2.BellReduction
