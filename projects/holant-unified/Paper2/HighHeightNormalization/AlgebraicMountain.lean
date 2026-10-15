import Paper2.HighHeightNormalization.CardNetwork

/-! Exact algebraic bookkeeping for the complete mountain under concrete
finite binary attachments.  The central tensor is used only as a coefficient
table and is not asserted to be independently realizable. -/
namespace Paper2.HighHeightNormalization
set_option backward.isDefEq.respectTransparency false
open Tractable CommonPhase MatchingPropagation EndpointSelfLoop Paper2.RelativeEO

/-- The complete algebraic coefficient table, including both endpoints. -/
noncomputable def algebraicMountain {n : ℕ} (a b : AlgebraicComplex)
    (F : Signature AlgebraicComplex n) : Signature AlgebraicComplex n := by
  classical
  exact fun x => (if x = (fun _ => false) then a else 0) +
    (if x = (fun _ => true) then b else 0) + F x

theorem algebraicMountain_coe {n : ℕ} (a b : AlgebraicComplex)
    (F : Signature AlgebraicComplex n) :
    (fun x => (algebraicMountain a b F x : ℂ)) =
      completeMountain (a : ℂ) (b : ℂ) (fun x => (F x : ℂ)) := by
  funext x
  classical
  unfold algebraicMountain completeMountain
  split_ifs <;> rfl

theorem coe_chargeLayer {n : ℕ} (F : Signature AlgebraicComplex n) (c : ℤ) :
    Tensor.ChargeLayer (fun x => (F x : ℂ)) c ↔ Tensor.ChargeLayer F c := by
  constructor <;> intro h x hx
  · apply h x
    intro hz
    exact hx (Subtype.ext hz)
  · apply h x
    intro hz
    apply hx
    change (F x : ℂ) = 0
    rw [hz]
    rfl

theorem coe_tensor_nonzero {ι : Type} (F : Tensor AlgebraicComplex ι) :
    (fun x => (F x : ℂ)) ≠ 0 ↔ F ≠ 0 := by
  constructor
  · intro h hz
    apply h
    funext x
    rw [hz]
    rfl
  · intro h hz
    apply h
    funext x
    exact Subtype.ext (congrFun hz x)

theorem coe_tensor_injective {ι : Type} {F G : Tensor AlgebraicComplex ι}
    (h : (fun x => (F x : ℂ)) = (fun x => (G x : ℂ))) : F = G := by
  funext x
  exact Subtype.ext (congrFun h x)

theorem algebraicMountain_loop {n : ℕ} (a b : AlgebraicComplex)
    (F : Signature AlgebraicComplex n) (e : PortPair (Fin n)) :
    contraction (fun x => (algebraicMountain a b F x : ℂ)) e =
      contraction (fun x => (F x : ℂ)) e := by
  rw [algebraicMountain_coe]
  exact contraction_completeMountain _ _ _ _

/-- Both endpoint scalars and the transformed central table are retained
exactly in the original algebraic field. -/
theorem attachmentSequence_algebraicMountain {n m : ℕ}
    (ports : Fin m → Fin n) (z : Fin m → AlgebraicComplex)
    (a b : AlgebraicComplex) (F : Signature AlgebraicComplex n) :
    attachmentSequence ports (fun j => algebraicBinary (z j)) (algebraicMountain a b F) =
      algebraicMountain ((∏ j,conjugateAlgebraic (z j))*a) ((∏ j,z j)*b)
        (attachmentSequence ports (fun j => algebraicBinary (z j)) F) := by
  apply coe_tensor_injective
  rw [attachmentSequence_coe,algebraicMountain_coe,attachFamily_completeMountain]
  rw [algebraicMountain_coe,attachmentSequence_coe]
  let φ : AlgebraicComplex →+* ℂ := (algebraicClosure ℚ ℂ).val.toRingHom
  have h₀ : (((∏ j,conjugateAlgebraic (z j))*a : AlgebraicComplex) : ℂ) =
      (∏ j,star (z j : ℂ)) * (a : ℂ) := by
    change φ ((∏ j,conjugateAlgebraic (z j))*a) = _
    rw [map_mul,map_prod]
    rfl
  have h₁ : (((∏ j,z j)*b : AlgebraicComplex) : ℂ) =
      (∏ j,(z j : ℂ)) * (b : ℂ) := by
    change φ ((∏ j,z j)*b) = _
    rw [map_mul,map_prod]
    rfl
  rw [h₀,h₁]

theorem attachmentSequence_central {n m : ℕ}
    (ports : Fin m → Fin n) (z : Fin m → AlgebraicComplex)
    (F : Signature AlgebraicComplex n) (hF : Tensor.ChargeLayer F 0) :
    Tensor.ChargeLayer (attachmentSequence ports (fun j => algebraicBinary (z j)) F) 0 := by
  apply (coe_chargeLayer _ _).mp
  rw [attachmentSequence_coe]
  exact attachFamily_chargeLayer _ _ _ _ ((coe_chargeLayer _ _).mpr hF)

theorem attachmentSequence_nonzero {n m : ℕ}
    (ports : Fin m → Fin n) (z : Fin m → AlgebraicComplex)
    (hz : ∀ j, z j ≠ 0) (F : Signature AlgebraicComplex n) (hF : F ≠ 0) :
    attachmentSequence ports (fun j => algebraicBinary (z j)) F ≠ 0 := by
  apply (coe_tensor_nonzero _).mp
  rw [attachmentSequence_coe]
  apply attachFamily_nonzero
  · intro j
    change (z j : ℂ) ≠ 0
    exact_mod_cast hz j
  · exact (coe_tensor_nonzero _).mpr hF

/-- The EO central table vanishes on the all-zero endpoint at positive arity. -/
theorem central_zero_word {n : ℕ} (hn : 0 < n)
    (F : Signature AlgebraicComplex n) (hF : Tensor.ChargeLayer F 0) :
    F (fun _ => false) = 0 := by
  by_contra h
  have hh := hF _ h
  simp only [doubledCharge,weight_false,Nat.cast_zero,mul_zero,zero_sub,Fintype.card_fin] at hh
  omega

theorem central_one_word {n : ℕ} (hn : 0 < n)
    (F : Signature AlgebraicComplex n) (hF : Tensor.ChargeLayer F 0) :
    F (fun _ => true) = 0 := by
  by_contra h
  have hh := hF _ h
  simp only [doubledCharge,weight_true,Fintype.card_fin] at hh
  omega

theorem algebraicMountain_isMountain {d : ℕ} (hd : 0 < d)
    (a b : AlgebraicComplex) (hab : a*b ≠ 0)
    (F : Signature AlgebraicComplex (2*d)) (hF : Tensor.ChargeLayer F 0) :
    IsMountain (algebraicMountain a b F) := by
  classical
  have hn : 0 < 2*d := by omega
  have hne : (fun _ : Fin (2*d) => false) ≠ (fun _ => true) := by
    intro h
    exact Bool.false_ne_true (congrFun h ⟨0,hn⟩)
  refine ⟨hd,?_,?_,?_⟩
  · intro x hx
    by_cases h₀ : x = (fun _ => false)
    · exact Or.inl h₀
    by_cases h₁ : x = (fun _ => true)
    · exact Or.inr (Or.inr h₁)
    have hxF : F x ≠ 0 := by simpa [algebraicMountain,h₀,h₁] using hx
    have hh := hF x hxF
    have ht := twice_halfCharge (by simpa using even_two_mul d) x
    exact Or.inr (Or.inl (by omega))
  · simpa [algebraicMountain,hne,central_zero_word hn F hF] using left_ne_zero_of_mul hab
  · simpa [algebraicMountain,hne.symm,central_one_word hn F hF] using right_ne_zero_of_mul hab

/-- The exact central restriction is EO independently of realizability. -/
theorem centralRestriction_chargeLayer {n : ℕ} (M : Signature AlgebraicComplex n) :
    Tensor.ChargeLayer (Signature.centralRestriction M) 0 := by
  intro x hx
  have hh : 2 * weight x = n := by
    by_contra h
    exact hx (by simp [Signature.centralRestriction,h])
  simp only [doubledCharge,Fintype.card_fin]
  omega

/-- Every literal mountain is exactly its original two endpoint coefficients
plus its central restriction.  All arities and all coefficients are retained. -/
theorem mountain_central_decomposition {d : ℕ}
    (M : Signature AlgebraicComplex (2*d)) (hM : IsMountain M) :
    M = algebraicMountain (M (fun _ => false)) (M (fun _ => true))
      (Signature.centralRestriction M) := by
  classical
  have hd := hM.height_pos
  have hn : 0 < 2*d := by omega
  have hne : (fun _ : Fin (2*d) => false) ≠ (fun _ => true) := by
    intro h
    exact Bool.false_ne_true (congrFun h ⟨0,hn⟩)
  funext x
  by_cases h₀ : x = (fun _ => false)
  · subst x
    simp [algebraicMountain,Signature.centralRestriction,hne,weight_false] <;> omega
  by_cases h₁ : x = (fun _ => true)
  · subst x
    simp [algebraicMountain,Signature.centralRestriction,hne.symm,weight_true] <;> omega
  by_cases hc : 2 * weight x = 2*d
  · simp [algebraicMountain,Signature.centralRestriction,h₀,h₁,hc]
  · have hz : M x = 0 := by
      by_contra hx
      rcases hM.support_layers x hx with h | h | h
      · exact h₀ h
      · have hw := (halfCharge_eq_zero_iff x).mp h
        exact hc (by omega)
      · exact h₁ h
    simp [algebraicMountain,Signature.centralRestriction,h₀,h₁,hc,hz]

end Paper2.HighHeightNormalization
