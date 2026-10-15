import Paper2.HighHeightNormalization.BinaryMating
import Paper2.Mountain

/-! Finite sequences of actual ordered native-X binary attachments. -/
namespace Paper2.HighHeightNormalization
open MatchingPropagation CommonPhase EndpointSelfLoop
variable {ι : Type}

/-- A finite sequence consisting only of the concrete attachments above. -/
noncomputable def attachFamily : {m : ℕ} → (Fin m → ι) →
    (Fin m → ℂ) → Tensor ℂ ι → Tensor ℂ ι
  | 0, _, _, F => F
  | m+1, ports, z, F => attach (ports 0) (binary (z 0))
      (attachFamily (fun j : Fin m => ports j.succ) (fun j => z j.succ) F)

/-- Its complete coefficient table is the product of the displayed nonzero
diagonal weights, with every original scalar retained. -/
theorem attachFamily_apply {m : ℕ} (ports : Fin m → ι) (z : Fin m → ℂ)
    (F : Tensor ℂ ι) (x : ι → Bool) :
    attachFamily ports z F x = (∏ j, matingWeight (z j) (x (ports j))) * F x := by
  induction m with
  | zero => simp [attachFamily]
  | succ m ih =>
    rw [attachFamily,attach_binary,ih]
    simp only [Fin.prod_univ_succ]
    ring

theorem attachFamily_support {m : ℕ} (ports : Fin m → ι) (z : Fin m → ℂ)
    (hz : ∀ j, z j ≠ 0) (F : Tensor ℂ ι) (x : ι → Bool) :
    attachFamily ports z F x ≠ 0 ↔ F x ≠ 0 := by
  rw [attachFamily_apply]
  have hp : (∏ j, matingWeight (z j) (x (ports j))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _ => matingWeight_ne_zero (hz j) _)
  simp [hp]

theorem attachFamily_nonzero {m : ℕ} (ports : Fin m → ι) (z : Fin m → ℂ)
    (hz : ∀ j, z j ≠ 0) (F : Tensor ℂ ι) (hF : F ≠ 0) : attachFamily ports z F ≠ 0 := by
  intro he
  apply hF
  funext x
  have hh := congrFun he x
  have hn : ¬attachFamily ports z F x ≠ 0 := by simpa using hh
  change F x = 0
  simpa only [not_not] using mt (attachFamily_support ports z hz F x).mpr hn

theorem attachFamily_chargeLayer [Fintype ι] {m : ℕ}
    (ports : Fin m → ι) (z : Fin m → ℂ) (F : Tensor ℂ ι)
    (k : ℤ) (hF : Tensor.ChargeLayer F k) : Tensor.ChargeLayer (attachFamily ports z F) k := by
  intro x hx
  apply hF x
  intro hz
  apply hx
  rw [attachFamily_apply,hz,mul_zero]

theorem attachFamily_halfChargeDivisible [Fintype ι] {m : ℕ}
    (ports : Fin m → ι) (z : Fin m → ℂ) (F : Tensor ℂ ι)
    (d : ℤ) (hF : Tensor.HalfChargeDivisible F d) :
    Tensor.HalfChargeDivisible (attachFamily ports z F) d := by
  intro x hx
  apply hF x
  intro hz
  apply hx
  rw [attachFamily_apply,hz,mul_zero]

/-- The complete mountain, not merely its formal central layer, retains both
actual endpoint coefficients and its support layers under every attachment. -/
theorem attachFamily_mountain {d m : ℕ} (ports : Fin m → Fin (2*d))
    (z : Fin m → ℂ) (hz : ∀ j, z j ≠ 0) (M : Signature ℂ (2*d))
    (hM : IsMountain M) : IsMountain (attachFamily ports z M) := by
  refine ⟨hM.height_pos,?_,?_,?_⟩
  · intro x hx
    exact hM.support_layers x ((attachFamily_support ports z hz M x).mp hx)
  · exact (attachFamily_support ports z hz M _).mpr hM.zero_ne_zero
  · exact (attachFamily_support ports z hz M _).mpr hM.one_ne_zero

/-- Attachments away from a deleted pair commute with its actual two-state sum. -/
theorem loop_attachFamily {m : ℕ} (e : PortPair ι)
    (ports : Fin m → Remaining e.first e.second) (z : Fin m → ℂ)
    (F : Tensor ℂ ι) (x : Remaining e.first e.second → Bool) :
    contraction (attachFamily (fun j => (ports j).val) z F) e x =
      (∏ j, matingWeight (z j) (x (ports j))) * contraction F e x := by
  change (∑ t : Bool, attachFamily (fun j => (ports j).val) z F
      (extendPair e.first e.second e.distinct x t)) = _
  simp only [attachFamily_apply,extend_other e x _ _ (ports _).property.1 (ports _).property.2]
  rw [← Finset.mul_sum]
  rfl

/-- Mating one endpoint of every factor cancels every relative coefficient. -/
theorem matching_mating (P : Matching ι) (z : Fin P.count → ℂ) (c : ℂ)
    (x : ι → Bool) :
    (∏ j, matingWeight (z j) (x (P.ports (j,false)))) *
      product P z (fun j => star (z j)) c x =
        (c * ∏ j, z j * star (z j)) * literal P ℂ x := by
  rw [product_coeff_literal]
  have hp : (∏ j, matingWeight (z j) (x (P.ports (j,false)))) *
      (∏ j, if x (P.ports (j,false)) then star (z j) else z j) =
        ∏ j, z j * star (z j) := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro j hj
    cases x (P.ports (j,false)) <;> simp [matingWeight,mul_comm]
  calc
    _ = (c * ((∏ j, matingWeight (z j) (x (P.ports (j,false)))) *
        (∏ j, if x (P.ports (j,false)) then star (z j) else z j))) * literal P ℂ x := by ring
    _ = _ := by rw [hp]

/-- The initial normalization of a selected nonzero ARS pair contraction is an
explicit finite sequence of native-X attachments to its original factor ports. -/
theorem normalize_selected_loop (F : Tensor ℂ ι) (e : PortPair ι)
    (P : Matching (Remaining e.first e.second)) (z : Fin P.count → ℂ) (c : ℂ)
    (hc : c ≠ 0) (hz : ∀ j, z j ≠ 0)
    (he : contraction F e = product P z (fun j => star (z j)) c) :
    contraction (attachFamily (fun j => (P.ports (j,false)).val) z F) e =
      fun x => (c * ∏ j, z j * star (z j)) * literal P ℂ x := by
  funext x
  rw [loop_attachFamily,he]
  exact matching_mating P z c x

theorem normalize_selected_loop_isX (F : Tensor ℂ ι) (e : PortPair ι)
    (P : Matching (Remaining e.first e.second)) (z : Fin P.count → ℂ) (c : ℂ)
    (hc : c ≠ 0) (hz : ∀ j, z j ≠ 0)
    (he : contraction F e = product P z (fun j => star (z j)) c) :
    XAt (attachFamily (fun j => (P.ports (j,false)).val) z F) e := by
  refine ⟨P,c * ∏ j, z j * star (z j),?_,normalize_selected_loop F e P z c hc hz he⟩
  exact mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr (fun j _ =>
    mul_ne_zero (hz j) (by simpa using hz j)))

end Paper2.HighHeightNormalization
