import Paper2.RelativeEO.AttachmentPullback

/-! Exact projective-ARS preservation by finite algebraic binary mating.
The reverse implication cancels the actual nonzero diagonal coefficient at
each ordered input; no synthesized conjugate tensor is used as a resource. -/
namespace Paper2.RelativeEO
open Tractable HighHeightNormalization
open scoped BigOperators

theorem matingWeight_star_complement (z : ℂ) (b : Bool) :
    star (matingWeight z (!b)) = matingWeight z b := by
  cases b <;> simp [matingWeight]

theorem mating_diagonal_star_complement {m n : ℕ}
    (ports : Fin m → Fin n) (z : Fin m → ℂ) (x : Fin n → Bool) :
    star (∏ j, matingWeight (z j) (!(x (ports j)))) =
      ∏ j, matingWeight (z j) (x (ports j)) := by
  simp only [star_prod,matingWeight_star_complement]

/-- The same algebraic normalizing scalar works before and after all finite
ordered attachments. Nonvanishing is essential for the reverse implication. -/
theorem attachmentSequence_projectiveARS_iff {m n : ℕ}
    (ports : Fin m → Fin n) (z : Fin m → AlgebraicComplex)
    (hz : ∀ j, z j ≠ 0) (f : Signature AlgebraicComplex n) :
    ProjectiveARS (attachmentSequence (K := AlgebraicComplex) ports (fun j => algebraicBinary (z j)) f) ↔
      ProjectiveARS f := by
  have he (x : Fin n → Bool) :
      (attachmentSequence (K := AlgebraicComplex) ports (fun j => algebraicBinary (z j)) f x : ℂ) =
        (∏ j, matingWeight (z j : ℂ) (x (ports j))) * (f x : ℂ) := by
    have h := congrFun (attachmentSequence_coe ports z f) x
    exact h.trans (attachFamily_apply ports (fun j => (z j : ℂ)) (fun y => (f y : ℂ)) x)
  have hdiag (x : Fin n → Bool) :
      (∏ j, matingWeight (z j : ℂ) (x (ports j))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j _
    apply matingWeight_ne_zero
    exact_mod_cast hz j
  constructor
  · rintro ⟨c,hc,hs⟩
    refine ⟨c,hc,fun x => ?_⟩
    have hh := hs x
    rw [he,he,star_mul,star_mul,mating_diagonal_star_complement] at hh
    apply mul_left_cancel₀ (hdiag x)
    calc
      _ = (c : ℂ)⁻¹ * ((∏ j, matingWeight (z j : ℂ) (x (ports j))) * (f x : ℂ)) := by ring
      _ = _ := hh
      _ = (∏ j, matingWeight (z j : ℂ) (x (ports j))) *
          star ((c : ℂ)⁻¹ * (f (fun i => !(x i)) : ℂ)) := by rw [star_mul]; ring
  · rintro ⟨c,hc,hs⟩
    refine ⟨c,hc,fun x => ?_⟩
    rw [he,he,star_mul,star_mul,mating_diagonal_star_complement]
    have hh := hs x
    rw [star_mul] at hh
    calc
      _ = (∏ j, matingWeight (z j : ℂ) (x (ports j))) *
          ((c : ℂ)⁻¹ * (f x : ℂ)) := by ring
      _ = (∏ j, matingWeight (z j : ℂ) (x (ports j))) *
          (star (c : ℂ)⁻¹ * star (f (fun i => !(x i)) : ℂ)) := by rw [hh,star_inv₀]; ring
      _ = _ := by rw [star_inv₀]; ring

end Paper2.RelativeEO
