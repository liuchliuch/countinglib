import ComplexCSP.Algebra.LegalPurificationTables

/-! # A genuine common phase exponent for finitely many pure entries -/
namespace ComplexCSP.PurePowerExponent
open scoped BigOperators
open GeneratingSet

/-- The exponent is constructed from the finite set of actual phase orders,
then doubled. Zero entries require no special purity assumption. -/
theorem exists_power_norm {A : Type} [Fintype A] (w : A → ℂ)
    (hp : ∀ a, IsPureValue (w a)) :
    ∃ N : ℕ, 2 ≤ N ∧ 2 ∣ N ∧ ∀ a, w a^N = (‖w a‖ : ℂ)^N := by
  classical
  choose n ζ hζ hw using hp
  let P := ∏ a, orderOf (ζ a)
  have hP : 0<P := Finset.prod_pos (fun a _ => (hζ a).orderOf_pos)
  refine ⟨2*P,by omega,by exact dvd_mul_right 2 P,?_⟩
  intro a
  have hd : orderOf (ζ a) ∣ 2*P :=
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem (fun a => orderOf (ζ a)) (Finset.mem_univ a)) 2
  obtain ⟨q,hq⟩ := hd
  have hpow : ζ a^(2*P)=1 := by rw [hq,pow_mul,pow_orderOf_eq_one,one_pow]
  have hn : ‖w a‖ = (n a : ℝ) := by rw [hw a]; simp [(hζ a).norm_eq_one]
  rw [hn,hw a,mul_pow,hpow,mul_one]
  norm_cast

/-- Actual legal purification data supplies the pure normalization and then a
common even phase exponent. No caller root-order bound is assumed. -/
theorem exists_legal_power_norm {X D : Type} [Fintype X] [Fintype D]
    {S : Finset ℂˣ} (L : LegalGeneratingSet S) (G : X → D → ℂ)
    (hG : LegalGeneratingSet.ContainsTable S G) :
    ∃ s N : ℕ, 0<s ∧ 2≤N ∧ 2∣N ∧ ∀ x z,
      ((s : ℂ)*L.purifyTable G hG x z)^N =
        (‖(s : ℂ)*L.purifyTable G hG x z‖ : ℂ)^N := by
  obtain ⟨s,hs,hpure⟩ := L.table_exists_pure_normalization G hG
  obtain ⟨N,hN,heven,hpow⟩ := exists_power_norm
    (fun p : X × D => (s : ℂ)*L.purifyTable G hG p.1 p.2)
    (fun p => hpure p.1 p.2)
  exact ⟨s,N,hs,hN,heven,fun x z => hpow (x,z)⟩

/-- The positive normalization cancels from the power/norm identity. Thus the
actual unscaled printed purification has a common even phase exponent too. -/
theorem exists_legal_power_norm_unscaled {X D : Type} [Fintype X] [Fintype D]
    {S : Finset ℂˣ} (L : LegalGeneratingSet S) (G : X → D → ℂ)
    (hG : LegalGeneratingSet.ContainsTable S G) :
    ∃ N : ℕ, 2≤N ∧ 2∣N ∧ ∀ x z,
      (L.purifyTable G hG x z)^N = (‖L.purifyTable G hG x z‖ : ℂ)^N := by
  obtain ⟨s,N,hs,hN,heven,hpow⟩ := exists_legal_power_norm L G hG
  refine ⟨N,hN,heven,?_⟩
  intro x z
  have hs0 : (s : ℂ)≠0 := by exact_mod_cast ne_of_gt hs
  apply mul_left_cancel₀ (pow_ne_zero N hs0)
  have h := hpow x z
  simpa only [mul_pow,norm_mul,Complex.norm_natCast,Complex.ofReal_mul,
    Complex.ofReal_natCast] using h

end ComplexCSP.PurePowerExponent
