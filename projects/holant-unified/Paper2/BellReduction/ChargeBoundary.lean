import Paper2.Certificates.BellNetworkClosures
import Paper2.Charge

/-! The high-charge promise is inherited by actual boundary networks, including
complex coefficients, disconnected gadgets, loops, and cancellation. -/
namespace Paper2.BellReduction
open Bell Bell.Closures
variable {K : Type} [CommRing K]

/-- Exactly the ambient high-charge hypothesis used in source Lemma 8.12. -/
def HighCharge (F : SignatureFamily K) : Prop :=
  ∀ f ∈ F, Even f.1 ∧ Tensor.HalfChargeDivisible f.2 4

/-- Adjoining Y preserves the charge promise without an ARS hypothesis. -/
theorem highCharge_insert_y {F : SignatureFamily K} (hF : HighCharge F) :
    HighCharge (insert (⟨2, fun x => Y (x 0) (x 1)⟩ : AnySignature K) F) := by
  intro f hf
  rcases hf with rfl | hf
  · refine ⟨by exact ⟨1,rfl⟩,?_⟩
    intro x hx
    have h : x 0 ≠ x 1 := by
      intro he
      apply hx
      simp [Y,ordered,he]
    have hc : halfCharge x = 0 := by
      simp only [halfCharge,Fintype.card_fin,weight,Fin.sum_univ_succ]
      cases h0 : x 0 <;> cases h1 : x 1 <;> simp_all
    rw [hc]
    exact dvd_zero _
  · exact hF f hf

/-- A supported half-charge divisible by four cannot fit on fewer than eight
even boundary ports unless it is zero. -/
theorem small_boundary_eo {n : ℕ} (N : Network K n) {F : SignatureFamily K}
    (hn : n < 8) (heven : Even n) (hF : HighCharge F)
    (hU : N.Uses F) (hX : N.NativeX) : Tensor.ChargeLayer N.denote 0 := by
  have hd := N.denote_halfChargeDivisible heven (fun v => (hF _ (hU v)).1) hX 4
    (fun v => (hF _ (hU v)).2)
  intro x hx
  have hw := weight_le_card x
  have h := hd x hx
  obtain ⟨k,hk⟩ := h
  have ht := twice_halfCharge (by simpa using heven) x
  obtain ⟨r,hr⟩ := heven
  simp only [halfCharge,Fintype.card_fin] at hk ht
  simp only [Fintype.card_fin] at hw
  omega

/-- The one-I branch is zero on the literal two-port boundary network. -/
theorem one_i_network_zero (N : Network K 2) {F : SignatureFamily K}
    (hF : HighCharge F) (hU : N.Uses F) (hX : N.NativeX) :
    Kernel.pair (fun a b => N.denote ![a,b]) I = 0 := by
  have hEO := small_boundary_eo N (by decide) (by decide) hF hU hX
  apply one_i_zero
  · by_contra h
    have hc := hEO ![false,false] h
    norm_num [show (![false,false] : Fin 2 → Bool) = (fun _ => false) by decide, doubledCharge] at hc
  · by_contra h
    have hc := hEO ![true,true] h
    norm_num [show (![true,true] : Fin 2 → Bool) = (fun _ => true) by decide, doubledCharge] at hc

/-- Source Q8.34 follows for every actual residual graph, with its EO premise
derived from the original ambient language rather than supplied separately. -/
theorem two_i_network_queries_of_highCharge (N : Network K 4) {F : SignatureFamily K}
    (hF : HighCharge F) (hU : N.Uses F) (hX : N.NativeX) :
    (2 : K) * fourPair N.denote I I = (close13 N).denote Fin.elim0 +
      (close14 N).denote Fin.elim0 - (close12 N).denote Fin.elim0 := by
  apply two_i_network_queries
  intro x hx
  by_contra hn
  have hc := small_boundary_eo N (by decide) (by decide) hF hU hX x hn
  have hw : weight x = (x 0).toNat + (x 1).toNat + (x 2).toNat + (x 3).toNat := by
    exact (by decide +kernel : ∀ y : Fin 4 → Bool, weight y =
      (y 0).toNat + (y 1).toNat + (y 2).toNat + (y 3).toNat) x
  simp only [doubledCharge,Fintype.card_fin,hw] at hc
  omega

end Paper2.BellReduction
