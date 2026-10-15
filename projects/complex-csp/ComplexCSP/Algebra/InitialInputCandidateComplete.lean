import ComplexCSP.Algebra.InitialInputCandidate

/-!
# Existence of accepted initial-conversion candidates

The finite candidates are derived from actual algebraic input descriptions,
exact-field primitive coordinates, and simultaneous rational root/image
certificates. No conversion-success hypothesis or candidate oracle is used.
-/
set_option backward.isDefEq.respectTransparency false

namespace ComplexCSP.AlgebraicEncoding
open Polynomial EncodedNumberField ComplexRootCertificates

/-- The mapped integral primitive polynomial has only simple complex roots. -/
theorem integralPresentation_complex_separable
    {K : Type} [Field K] [NumberField K] (P : IntegralPrimitivePresentation K) :
    (P.polynomial.map (Int.castRingHom ℂ)).Separable := by
  have hs : ((P.polynomial.map (Int.castRingHom ℚ)).map (Rat.castHom ℂ)).Separable := by
    rw [P.map_eq_minpoly]
    exact (minpoly.irreducible P.basis.isIntegral_gen).separable.map
  have hm : (P.polynomial.map (Int.castRingHom ℚ)).map (Rat.castHom ℂ) =
      P.polynomial.map (Int.castRingHom ℂ) := by
    ext i
    simp
  exact hm ▸ hs

/-- Every correctly represented finite input family has an accepted literal
common-field candidate, including its primitive-expression and image witnesses. -/
theorem exists_initialInputCandidate {m : ℕ} (input : Fin m → AlgebraicInput)
    (z : Fin m → ℂ) (hz : ∀ i, (input i).Represents (z i)) :
    ∃ C : InitialInputCandidate m, C.test input = true := by
  have halg : ∀ i, IsAlgebraic ℚ (z i) := fun i => (hz i).isAlgebraic
  letI := initialInputField_numberField z halg
  obtain ⟨P, coordinates, expression, hcoordinates, hexpression⟩ :=
    exists_initial_primitive_coordinates z halg
  let tail : Fin P.basis.dim → ℤ := fun i => P.polynomial.coeff i.val
  have hd : P.polynomial.natDegree = P.basis.dim :=
    EffectiveRoots.polynomial_natDegree_eq_dim P.basis P.polynomial P.map_eq_minpoly
  have hv : validTail tail = true := by
    apply (MonicIrreducibility.irreducibleMonicTail_correct_of_coeff tail
      P.polynomial P.monic hd (fun _ => rfl)).mpr
    rw [P.map_eq_minpoly]
    exact minpoly.irreducible P.basis.isIntegral_gen
  letI : Fact (Element.Valid P.basis.dim (EffectiveRoots.coefficientRelation tail)) :=
    ⟨validTail_sound tail hv⟩
  have hrootK : aeval P.basis.gen P.polynomial = 0 := by
    rw [← aeval_map_algebraMap ℚ]
    change aeval P.basis.gen (P.polynomial.map (Int.castRingHom ℚ)) = 0
    rw [P.map_eq_minpoly, minpoly.aeval]
  have hrelation : P.basis.gen ^ P.basis.dim =
      interpret P.basis.gen (EffectiveRoots.coefficientRelation tail) := by
    rw [EffectiveRoots.coefficientRelation_eq tail P.polynomial (fun _ => rfl)]
    exact EffectiveRoots.generator_relation P.basis P.polynomial P.monic hrootK P.map_eq_minpoly
  let M : Element.Model P.basis.dim (EffectiveRoots.coefficientRelation tail) :=
    ⟨initialInputField z, inferInstance, inferInstance, P.basis.gen,
      P.basis.basis, P.basis.basis_eq_pow, hrelation⟩
  let Φ := (algebraMap (initialInputField z) ℂ).comp M.valueRingEquiv.toRingHom
  have hΦgen : Φ (Element.generator (c := EffectiveRoots.coefficientRelation tail)) =
      (P.basis.gen : ℂ) := congrArg (algebraMap (initialInputField z) ℂ) M.value_generator
  have hΦcoordinate (i : Fin m) :
      Φ (⟨coordinates i⟩ : Element P.basis.dim (EffectiveRoots.coefficientRelation tail)) = z i := by
    change algebraMap (initialInputField z) ℂ (interpret P.basis.gen (coordinates i)) = _
    simp only [interpret, map_sum, map_mul, map_pow,
      ← IsScalarTower.algebraMap_apply ℚ (initialInputField z) ℂ]
    have he := hcoordinates i
    simp only [interpret] at he
    exact he
  have hdenote : ComplexRootCertificates.denote (ofMonicIntTail tail) =
      P.polynomial.map (Int.castRingHom ℂ) := denote_ofMonicIntTail_eq tail P.polynomial P.monic hd
        (fun _ => rfl)
  have hroot : (ComplexRootCertificates.denote (ofMonicIntTail tail)).eval (P.basis.gen : ℂ) = 0 := by
    rw [hdenote, Polynomial.eval_map]
    change aeval (algebraMap (initialInputField z) ℂ P.basis.gen) P.polynomial = 0
    rw [aeval_algebraMap_apply, hrootK, map_zero]
  have hsimple : (ComplexRootCertificates.denote (ofMonicIntTail tail)).derivative.eval
      (P.basis.gen : ℂ) ≠ 0 := by
    have hs : (ComplexRootCertificates.denote (ofMonicIntTail tail)).Separable :=
      hdenote ▸ integralPresentation_complex_separable P
    simpa using hs.eval₂_derivative_ne_zero (RingHom.id ℂ) (by simpa using hroot)
  have hbox (i : Fin m) : (input i).rectangle.Contains
      ((ComplexRootCertificates.denote (ofRatVector (coordinates i))).eval (P.basis.gen : ℂ)) := by
    rw [eval_denote_ofRatVector]
    change (input i).rectangle.Contains (interpret (P.basis.gen : ℂ) (coordinates i))
    rw [hcoordinates i]
    exact (hz i).2.2.1
  obtain ⟨center, radius, _, _, _, hcert, himages⟩ := exists_certificates_of_simple_root
    (ofMonicIntTail tail) (P.basis.gen : ℂ) hroot hsimple (fun _ : Fin m => P.basis.dim)
    (fun i => ofRatVector (coordinates i)) (fun i => (input i).rectangle) hbox 1 (by norm_num)
  let C : InitialInputCandidate m := ⟨P.basis.dim, tail, coordinates, expression, center, radius⟩
  refine ⟨C, (C.test_spec input hv).mpr ?_⟩
  refine ⟨hcert, ?_, ?_⟩
  · intro i
    refine ⟨?_, himages i⟩
    apply Φ.injective
    rw [map_evalIntegerList, map_zero]
    change evalIntegerList (input i).coefficients
      (Φ (⟨coordinates i⟩ : Element P.basis.dim (EffectiveRoots.coefficientRelation tail))) = 0
    rw [hΦcoordinate]
    exact (hz i).2.1
  · apply Φ.injective
    rw [PolynomialPrograms.map_interpret, hΦgen]
    have hf : Φ.comp (algebraMap ℚ C.FieldType) = algebraMap ℚ ℂ := by
      ext q
      simp
    rw [hf]
    have hc : (fun i => Φ (C.coordinateValue i)) = z := funext hΦcoordinate
    rw [hc]
    exact hexpression

/-- No chosen complex values are needed in the public existence statement:
the semantic validity promise on each finite input description suffices. -/
theorem exists_initialInputCandidate_of_valid {m : ℕ} (input : Fin m → AlgebraicInput)
    (hinput : ∀ i, (input i).Valid) :
    ∃ C : InitialInputCandidate m, C.test input = true := by
  choose z hz using hinput
  exact exists_initialInputCandidate input z hz

end ComplexCSP.AlgebraicEncoding
