module
public import Paper2.Certificates.DihedralSupport.Classification
public import Mathlib.SetTheory.Cardinal.NatCard

/-! Exact counts of actual six-bit supports, rather than only counts of
their encodings. The word/mask bijection is proved for each bounded mask. -/
@[expose] public section
namespace Paper2.Certificates.DihedralSupport

noncomputable def maskSupportEquiv (M : Finset Nat)
    (hb : ∀ m ∈ M,m < 18446744073709551616) :
    {S : Support6 // encodeSupport S ∈ M} ≃ {m : Nat // m ∈ M} where
  toFun S := ⟨encodeSupport S.val,S.property⟩
  invFun m := ⟨fun x => m.val.testBit (index6 x),by
    rw [encodeSupport_decode m.val (hb _ m.property)]
    exact m.property⟩
  left_inv S := by
    apply Subtype.ext
    funext x
    exact encodeSupport_spec S.val x
  right_inv m := by
    apply Subtype.ext
    exact encodeSupport_decode m.val (hb _ m.property)

theorem support_family_card (M : Finset Nat)
    (hb : ∀ m ∈ M,m < 18446744073709551616) :
    Nat.card {S : Support6 // encodeSupport S ∈ M} = M.card := by
  calc
    _ = Nat.card {m : Nat // m ∈ M} := Nat.card_congr (maskSupportEquiv M hb)
    _ = M.card := by rw [Nat.card_eq_fintype_card,Fintype.card_coe]

theorem classified_bounded (m : Nat) (hm : m ∈ classifiedMasks) :
    m < 18446744073709551616 := ((admissible_iff_classified m).mpr hm).1

/-- The source count is literally the cardinality of the subtype of all
actual Boolean supports satisfying every actual port/xor projection test. -/
theorem admissible_support_count : Nat.card {S : Support6 // AdmissibleSupport S} = 873 := by
  let e := Equiv.subtypeEquivRight (fun S : Support6 =>
    (admissibleSupport_iff_mask S).trans (admissible_iff_classified (encodeSupport S)))
  calc
    _ = Nat.card {S : Support6 // encodeSupport S ∈ classifiedMasks} := Nat.card_congr e
    _ = classifiedMasks.card := support_family_card classifiedMasks classified_bounded
    _ = 873 := classifiedMasks_card

theorem affine_support_count : Nat.card {S : Support6 // encodeSupport S ∈ affineMasks} = 392 := by
  exact (support_family_card affineMasks (fun m hm => (affineMasks_positive_bounded m hm).2)).trans
    affineMasks_card

theorem orbit_support_count :
    Nat.card {S : Support6 //
      ∃ σ : Equiv.Perm (Fin 6),∃ b : SupportOrbit.Word,
        ∀ x,S x=SupportOrbit.sstar (SupportOrbit.wordAction σ b x)} = 480 := by
  let e := Equiv.subtypeEquivRight (fun S : Support6 => (SupportOrbit.support_orbit_iff S).symm)
  calc
    _ = Nat.card {S : Support6 // encodeSupport S ∈ SupportOrbit.orbitMasks} := Nat.card_congr e
    _ = SupportOrbit.orbitMasks.card := support_family_card _ (fun _ hm => SupportOrbit.orbit_lt hm)
    _ = 480 := SupportOrbit.orbitMasks_card

end Paper2.Certificates.DihedralSupport

