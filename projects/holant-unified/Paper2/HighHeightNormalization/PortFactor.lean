import Paper2.HighHeightNormalization.Attachments

/-! Actual coefficient comparisons for a single remaining ARS factor. -/
namespace Paper2.HighHeightNormalization
open MatchingPropagation CommonPhase EndpointSelfLoop
variable {ι : Type}

/-- Ordered coefficient of B(z), read at its first endpoint. -/
def phaseWeight (z : ℂ) (b : Bool) : ℂ := if b then star z else z

theorem phaseWeight_ne_zero {z : ℂ} (hz : z ≠ 0) (b : Bool) :
    phaseWeight z b ≠ 0 := by cases b <;> simpa [phaseWeight] using hz

/-- If a paired deletion hits only one matching factor, all other factors are
forced literal by its actual nonzero flat double contraction. -/
theorem paired_card_form (F : Tensor ℂ ι) (e r : PortPair ι) (her : e.Disjoint r)
    (hr : XAt F r) (P : Matching (Remaining e.first e.second))
    (z : Fin P.count → ℂ) (c : ℂ) (hc : c ≠ 0) (hz : ∀ j, z j ≠ 0)
    (he : contraction F e = product P z (fun j => star (z j)) c)
    (hm : mate P (e.residual r her).first = (e.residual r her).second) :
    ∃ (w C : ℂ), w ≠ 0 ∧ C ≠ 0 ∧
      (w = z (P.ports.symm (e.residual r her).first).1 ∨
       w = star (z (P.ports.symm (e.residual r her).first).1)) ∧
      contraction F e = fun x =>
        phaseWeight w (x (e.residual r her).first) * C * literal P ℂ x := by
  classical
  let a := (e.residual r her).first
  let j := (P.ports.symm a).1
  let b := (P.ports.symm a).2
  have ha : P.ports (j,b) = a := P.ports.apply_symm_apply a
  have hi : (P.ports.symm (e.residual r her).second).1 = j := by
    apply (index_eq_iff P _ a).mpr
    exact Or.inr hm.symm
  have hother : ∀ k, k ≠ j → z k = star (z k) := by
    intro k hk
    apply factor_eq_of_disjoint_X F e r her hr P z (fun k => star (z k)) c hz
      (fun k => by simpa using hz k) he k
    exact (avoids_iff_index P k _).mpr ⟨hk,by simpa only [hi] using hk⟩
  let w := if b then star (z j) else z j
  let C := c * ∏ k ∈ Finset.univ.erase j, z k
  refine ⟨w,C,?_,?_,?_,?_⟩
  · dsimp [w]
    cases b <;> simpa using hz j
  · exact mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr (fun k _ => hz k))
  · dsimp [w]
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  · rw [he]
    funext x
    rw [product_single P z (fun k => star (z k)) c j b hother,ha]
    change (if x a = b then z j else star (z j)) * C * literal P ℂ x = _
    have hw : (if x a = b then z j else star (z j)) = phaseWeight w (x a) := by
      dsimp [w,phaseWeight]
      cases b <;> cases x a <;> simp
    rw [hw]

/-- The surviving port weight factors out of the literal two-state sum. -/
theorem pairSum_phase (P : Matching ι) (a : ι) (z c : ℂ) (e : PortPair ι)
    (ha₁ : a ≠ e.first) (ha₂ : a ≠ e.second) (x : ι → Bool) :
    e.pairSum (fun y => phaseWeight z (y a) * c * literal P ℂ y) x =
      phaseWeight z (x a) * (c * e.pairSum (literal P ℂ) x) := by
  unfold PortPair.pairSum
  simp only [fill_other e x _ a ha₁ ha₂,Finset.mul_sum,mul_assoc]

private theorem cross_of_two_equalities {z w A B : ℂ} (hA : A ≠ 0)
    (h₀ : z * A = w * B) (h₁ : star z * A = star w * B) :
    star z * w = z * star w := by
  apply mul_right_cancel₀ hA
  calc
    star z * w * A = w * (star z * A) := by ring
    _ = w * (star w * B) := by rw [h₁]
    _ = star w * (w * B) := by ring
    _ = star w * (z * A) := by rw [← h₀]
    _ = z * star w * A := by ring

/-- Comparing a supported assignment and its complement extracts the true
ordered coefficient ratio, even with unrelated nonzero overall scalars. -/
theorem phase_ratio_of_equal (a : ι) (z w : ℂ) (H J : Tensor ℂ ι)
    (hH : ∀ x, H (fun i => !(x i)) = H x)
    (hJ : ∀ x, J (fun i => !(x i)) = J x)
    (he : ∀ x, phaseWeight z (x a) * H x = phaseWeight w (x a) * J x)
    (hnz : ∃ x, phaseWeight z (x a) * H x ≠ 0) :
    star z * w = z * star w := by
  obtain ⟨x,hx⟩ := hnz
  have hA : H x ≠ 0 := by intro h; simp [h] at hx
  have h₀ := he x
  have h₁ := he (fun i => !(x i))
  rw [hH,hJ] at h₁
  cases hb : x a <;> simp only [hb,phaseWeight,Bool.not_false,Bool.not_true] at h₀ h₁
  · exact cross_of_two_equalities hA h₀ h₁
  · exact cross_of_two_equalities hA h₁ h₀

theorem phase_ratio_trans {z w v : ℂ} (hw : w ≠ 0)
    (hzw : star z * w = z * star w) (hwv : star w * v = w * star v) :
    star z * v = z * star v := by
  apply mul_right_cancel₀ hw
  calc
    star z * v * w = (star z * w) * v := by ring
    _ = (z * star w) * v := by rw [hzw]
    _ = z * (star w * v) := by ring
    _ = z * (w * star v) := by rw [hwv]
    _ = z * star v * w := by ring

/-- A concrete attachment normalizes any single surviving factor whose
ordered coefficient ratio has been proved to agree with the attached factor. -/
theorem attach_phase_isX (P : Matching ι) (a : ι) (z w c : ℂ)
    (hz : z ≠ 0) (hw : w ≠ 0) (hc : c ≠ 0)
    (hr : star z * w = z * star w) :
    IsX (attach a (binary z) (fun x => phaseWeight w (x a) * c * literal P ℂ x)) := by
  refine ⟨P,(star z * w) * c,mul_ne_zero (mul_ne_zero (by simpa using hz) hw) hc,?_⟩
  funext x
  rw [attach_binary]
  have h : matingWeight z (x a) * phaseWeight w (x a) = star z * w := by
    cases x a
    · rfl
    · exact hr.symm
  calc
    _ = (matingWeight z (x a) * phaseWeight w (x a)) * c * literal P ℂ x := by ring
    _ = _ := by rw [h]

end Paper2.HighHeightNormalization
