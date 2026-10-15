import ComplexCSP.Algebra.EffectiveRootsEnumeration

/-!
# The computed root count supplies a small torsion exponent

The executable exponent is lcm(2, number of roots actually enumerated). The
proof identifies the computed coordinate set with a finite root group killed
by the already proved trace-box factorial. That abstract group is used only in
the proof; runtime enumeration never calls a noncomputable finite-type choice.
-/

namespace ComplexCSP.EffectiveRoots

/-- A runtime even exponent, computed from the actual enumerated root count. -/
def computedRootExponent (n : ℕ) (p : Polynomial ℤ) : ℕ :=
  Nat.lcm 2 (rootCoordinates n p).card

variable {K : Type*} [Field K] [NumberField K]

theorem rootCoordinates_nonempty (pb : PowerBasis ℚ K) (p : Polynomial ℤ)
    (hp : p.Monic) (hroot : Polynomial.aeval pb.gen p = 0)
    (hpoly : p.map (Int.castRingHom ℚ) = minpoly ℚ pb.gen) :
    (rootCoordinates pb.dim p).Nonempty := by
  obtain ⟨a, ha, _⟩ := every_root_is_enumerated pb p hp hroot hpoly 1 (isOfFinOrder_iff_pow_eq_one.mpr ⟨1, by decide, one_pow 1⟩)
  exact ⟨a, ha⟩

/-- Every root is killed by the number of roots that the runtime algorithm
actually enumerates, without a factorial-sized runtime power. -/
theorem root_pow_enumerated_card (pb : PowerBasis ℚ K) (p : Polynomial ℤ)
    (hp : p.Monic) (hroot : Polynomial.aeval pb.gen p = 0)
    (hpoly : p.map (Int.castRingHom ℚ) = minpoly ℚ pb.gen)
    (ζ : K) (hζ : IsOfFinOrder ζ) : ζ ^ (rootCoordinates pb.dim p).card = 1 := by
  classical
  let E := candidateExponent (gramFromPolynomial pb.dim p) (integerCauchyBound p)
  have hE : 0 < E := Nat.factorial_pos _
  letI : NeZero E := ⟨ne_of_gt hE⟩
  let Roots := rootsOfUnity E K
  letI : Fintype Roots := Fintype.ofFinite Roots
  let f : Roots → ↥(rootCoordinates pb.dim p) := fun r ↦
    ⟨pb.basis.equivFun (r.val : K), (mem_rootCoordinates_iff pb p hp hroot hpoly _).mpr (by
      rw [EncodedNumberField.interpret_coordinates]
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨E, hE, (mem_rootsOfUnity' _ _).mp r.property⟩)⟩
  have hinj : Function.Injective f := by
    intro r s hrs
    apply Subtype.ext
    apply Units.ext
    apply pb.basis.equivFun.injective
    exact congrArg Subtype.val hrs
  have hsurj : Function.Surjective f := by
    intro a
    have ha := (mem_rootCoordinates_iff pb p hp hroot hpoly a.val).mp a.property
    let u := ha.unit
    have hu : u ∈ Roots := by
      apply (mem_rootsOfUnity' _ _).mpr
      exact root_pow_computed_exponent pb p hp hroot hpoly _ ha
    refine ⟨⟨u, hu⟩, ?_⟩
    apply Subtype.ext
    exact EncodedNumberField.coordinates_interpret pb a.val
  have hcard : Fintype.card Roots = (rootCoordinates pb.dim p).card := by
    simpa only [Fintype.card_coe] using Fintype.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)
  let u := hζ.unit
  have hu : u ∈ Roots := by
    apply (mem_rootsOfUnity' _ _).mpr
    exact root_pow_computed_exponent pb p hp hroot hpoly ζ hζ
  have hpow := pow_card_eq_one (x := (⟨u, hu⟩ : Roots))
  have hv := congrArg (fun r : Roots ↦ (r.val : K)) hpow
  rw [← hcard]
  simp only [Subgroup.coe_pow, Units.val_pow_eq_pow_val, Subgroup.coe_one, Units.val_one] at hv
  exact hv

theorem computedRootExponent_ge_two (pb : PowerBasis ℚ K) (p : Polynomial ℤ)
    (hp : p.Monic) (hroot : Polynomial.aeval pb.gen p = 0)
    (hpoly : p.map (Int.castRingHom ℚ) = minpoly ℚ pb.gen) :
    2 ≤ computedRootExponent pb.dim p :=
  Nat.le_lcm_left 2 (Finset.card_pos.mpr (rootCoordinates_nonempty pb p hp hroot hpoly))

theorem computedRootExponent_even (n : ℕ) (p : Polynomial ℤ) :
    Even (computedRootExponent n p) := even_iff_two_dvd.mpr (Nat.dvd_lcm_left 2 _)

/-- The runtime polynomial-derived exponent satisfies precisely the torsion
condition needed by the finite row-detector theorem. -/
theorem computedRootExponent_killsTorsion (pb : PowerBasis ℚ K) (p : Polynomial ℤ)
    (hp : p.Monic) (hroot : Polynomial.aeval pb.gen p = 0)
    (hpoly : p.map (Int.castRingHom ℚ) = minpoly ℚ pb.gen) :
    RowDetector.KillsTorsion K (computedRootExponent pb.dim p) := by
  intro ζ hζ
  obtain ⟨m, hm⟩ := Nat.dvd_lcm_right 2 (rootCoordinates pb.dim p).card
  change ζ ^ Nat.lcm 2 (rootCoordinates pb.dim p).card = 1
  rw [hm, pow_mul, root_pow_enumerated_card pb p hp hroot hpoly ζ hζ, one_pow]

end ComplexCSP.EffectiveRoots
