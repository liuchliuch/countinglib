import Paper2.HighHeightNormalization.FiniteAttachments
import Paper2.HighHeightNormalization.Seed
import Paper2.CommonPhase.Recovery

/-! Ordered exact-input contraction cards and their actual one-loop graphs.
Charge conservation is proved at the graph boundary; the central tensor is
never asserted to be a separately available vertex. -/
namespace Paper2.HighHeightNormalization
open EndpointSelfLoop CommonPhase MatchingPropagation Tractable
variable {K : Type} [CommRing K] {n : ℕ}

/-- A native-X self-loop on two named ports of an actual gadget is again an
actual gadget over precisely the same language. -/
theorem contraction_realizable {F : SignatureFamily K} (M : Signature K n)
    (e : PortPair (Fin n)) (hM : NetworkRealizable F M) :
    NetworkRealizable F (loop e.first e.second e.distinct M) :=
  (hM.reindex (splitPorts e.first e.second e.distinct)).selfLoop

/-- An ordered table on all and only the undeleted occurrences. -/
noncomputable def cardTable (M : Signature K n) (e : PortPair (Fin n)) :
    Signature K (Fintype.card (Remaining e.first e.second)) :=
  Tensor.reindex (Fintype.equivFin (Remaining e.first e.second))
    (loop e.first e.second e.distinct M)

theorem cardTable_realizable {F : SignatureFamily K} (M : Signature K n)
    (e : PortPair (Fin n)) (hM : NetworkRealizable F M) :
    NetworkRealizable F (cardTable M e) :=
  (contraction_realizable M e hM).reindex _

theorem cardTable_nonzero (M : Signature K n) (e : PortPair (Fin n)) :
    cardTable M e ≠ 0 ↔ loop e.first e.second e.distinct M ≠ 0 := by
  constructor
  · intro h hz
    apply h
    rw [cardTable,hz]
    rfl
  · intro h hz
    apply h
    funext x
    have hh := congrFun hz (fun i => x ((Fintype.equivFin (Remaining e.first e.second)).symm i))
    simpa [cardTable,Tensor.reindex] using hh

theorem cardTable_arity (e : PortPair (Fin n)) :
    Fintype.card (Remaining e.first e.second) + 2 = n := by
  simpa using remaining_card e.first e.second e.distinct

/-- The actual incidence equivalence forces even boundary arity when every
vertex has even arity.  Internal native-X edges use exactly two occurrences. -/
theorem network_even_boundary (N : Network K n)
    (h : ∀ v, Even (N.shape.arity v)) : Even n := by
  classical
  choose k hk using h
  have hc := Fintype.card_congr N.shape.ports
  simp only [Fintype.card_sigma,Fintype.card_fin,Fintype.card_sum,
    Fintype.card_prod,Fintype.card_bool] at hc
  have hs : (∑ v,N.shape.arity v) = (∑ v,k v) + (∑ v,k v) := by
    simp_rw [hk]
    rw [Finset.sum_add_distrib]
  rw [hs] at hc
  exact ⟨(∑ v,k v)-N.shape.edges,by omega⟩

theorem realizable_even_arity {F : SignatureFamily K}
    (heven : ∀ g ∈ F, Even g.1) (f : Signature K n)
    (hf : NetworkRealizable F f) : Even n := by
  obtain ⟨N,hU,_,_⟩ := hf.ordered
  exact network_even_boundary N (fun v => heven _ (hU v))

/-- A supported charge divisible by d cannot fit on an even boundary with
fewer than 2d ports unless that charge is exactly zero. -/
theorem small_boundary_chargeLayer {d : ℕ} (N : Network K n)
    {F : SignatureFamily K} (hn : n < 2*d) (heven : Even n)
    (hF : ∀ f ∈ F, Even f.1 ∧ Tensor.HalfChargeDivisible f.2 d)
    (hU : N.Uses F) (hX : N.NativeX) : Tensor.ChargeLayer N.denote 0 := by
  have hd := N.denote_halfChargeDivisible heven (fun v => (hF _ (hU v)).1) hX d
    (fun v => (hF _ (hU v)).2)
  intro x hx
  have hw := weight_le_card x
  have ht := twice_halfCharge (by simpa using heven) x
  obtain ⟨r,hr⟩ := heven
  simp only [Fintype.card_fin] at hw
  have hb : -(d : ℤ) < halfCharge x ∧ halfCharge x < (d : ℤ) := by
    simp only [halfCharge,Fintype.card_fin]
    omega
  have hz := eq_neg_or_zero_or_pos_of_dvd_of_bounds
    (by omega : (0 : ℤ) < d) (hd x hx) (le_of_lt hb.1) (le_of_lt hb.2)
  have hzero : halfCharge x = 0 := by omega
  rw [hzero] at ht
  omega

theorem realizable_small_boundary_chargeLayer {d : ℕ} {F : SignatureFamily K}
    (f : Signature K n) (hn : n < 2*d) (heven : Even n)
    (hF : ∀ g ∈ F, Even g.1 ∧ Tensor.HalfChargeDivisible g.2 d)
    (hf : NetworkRealizable F f) : Tensor.ChargeLayer f 0 := by
  obtain ⟨N,hU,hX,hN⟩ := hf.ordered
  rw [← hN]
  exact small_boundary_chargeLayer N hn heven hF hU hX

theorem realizable_small_boundary_eo {d : ℕ} {F : SignatureFamily K}
    (f : Signature K n) (hn : n < 2*d)
    (hF : ∀ g ∈ F, Even g.1 ∧ Tensor.HalfChargeDivisible g.2 d)
    (hf : NetworkRealizable F f) : Even n ∧ Tensor.ChargeLayer f 0 := by
  have he := realizable_even_arity (fun g hg => (hF g hg).1) f hf
  exact ⟨he,realizable_small_boundary_chargeLayer f hn he hF hf⟩

theorem cardTable_chargeLayer {d : ℕ} {F : SignatureFamily K}
    (M : Signature K (2*d)) (e : PortPair (Fin (2*d)))
    (hF : ∀ g ∈ F, Even g.1 ∧ Tensor.HalfChargeDivisible g.2 d)
    (hM : NetworkRealizable F M) : Tensor.ChargeLayer (cardTable M e) 0 := by
  have hc := cardTable_arity e
  have hlt : Fintype.card (Remaining e.first e.second) < 2*d := by omega
  have heven : Even (Fintype.card (Remaining e.first e.second)) := by
    refine ⟨d-1,?_⟩
    omega
  exact realizable_small_boundary_chargeLayer _ hlt heven hF (cardTable_realizable M e hM)

/-- Coercing exact algebraic coefficients retains every contraction summand. -/
theorem cardTable_coe (M : Signature AlgebraicComplex n) (e : PortPair (Fin n)) :
    (fun x => (cardTable M e x : ℂ)) = cardTable (fun x => (M x : ℂ)) e := by
  funext x
  exact (loop_map (algebraicClosure ℚ ℂ).val.toRingHom.toAddMonoidHom
    e.first e.second e.distinct M _).symm

end Paper2.HighHeightNormalization
