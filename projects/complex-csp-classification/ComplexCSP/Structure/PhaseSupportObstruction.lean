import ComplexCSP.Structure.PhaseRowNormalization

/-! # Zero-support removal and literal phase obstructions for arbitrary rows -/
noncomputable section
open Classical
namespace ComplexCSP.PhaseSupportObstruction
open scoped BigOperators
open PhasePowerAlgebra PhaseRowNormalization BlockOrthogonality RowTypes
variable {D : Type} [Fintype D]

private theorem sum_support (u f : D → ℂ) (hf : ∀ z,u z=0 → f z=0) :
    (∑ z : {z // u z≠0}, f z.val) = ∑ z,f z := by
  have hs := Fintype.sum_subtype_add_sum_subtype (fun z => u z≠0) f
  have hz : (∑ z : {z // ¬u z≠0}, f z.val)=0 := by
    apply Finset.sum_eq_zero
    intro z _
    exact hf z.val (not_ne_iff.mp z.property)
  simpa only [hz,add_zero] using hs

private theorem hermitian_support (u v : D → ℂ) (a : {z // u z≠0}) :
    hermitianSum (fun z : {z // u z≠0} => u z) (fun z => v z)
      (magnitudeBlock (fun z : {z // u z≠0} => u z) a) =
    hermitianSum u v (magnitudeBlock u a.val) := by
  simp only [hermitianSum,magnitudeBlock,Finset.sum_filter]
  apply sum_support u (fun z => if ‖u z‖=‖u a.val‖ then u z*star (v z) else 0)
  intro z hz
  simp [hz]

/-- Zero columns are discarded by a proved finite-sum identity, then restored.
The witness bound is the original domain size, not an assumed support bound. -/
theorem bounded_rows (u v : D → ℂ) (hu : u≠0)
    (hm : MagnitudeProportional u v) (K : ℕ) (hK : 0<K)
    (hpu : ∀ z,u z^K=(‖u z‖ : ℂ)^K) (hpv : ∀ z,v z^K=(‖v z‖ : ℂ)^K)
    (hind : ¬Proportional u v) (horth : ¬VectorBlockOrthogonal u v) :
    ∃ t : ℕ, 0<t ∧ t ≤ Fintype.card D ∧ StrictMinor u v (t*K) := by
  let S := {z // u z≠0}
  obtain ⟨z,hz⟩ := Function.ne_iff.mp hu
  letI : Nonempty S := ⟨⟨z,hz⟩⟩
  have hzero : ∀ z,u z=0 ↔ v z=0 := by
    intro z
    have he := magnitudeProportional_support_eq hm
    have := Set.ext_iff.mp he z
    simpa only [support,Set.mem_ofPred_eq,not_iff_not] using this
  let us : S → ℂ := fun z => u z
  let vs : S → ℂ := fun z => v z
  have hus : ∀ z,us z≠0 := fun z => z.property
  have hvs : ∀ z,vs z≠0 := fun z => (hzero z).not.mp z.property
  have hms : MagnitudeProportional us vs := by
    obtain ⟨c,hc,hm⟩ := hm
    exact ⟨c,hc,fun z => hm z⟩
  have hinds : ¬Proportional us vs := by
    rintro ⟨c,hc,he⟩
    apply hind
    refine ⟨c,hc,?_⟩
    intro z
    by_cases hz : u z=0
    · rw [hz,(hzero z).mp hz,mul_zero]
    · exact he ⟨z,hz⟩
  have horths : ¬VectorBlockOrthogonal us vs := by
    intro hh
    apply horth
    intro z hz
    have he := hh ⟨z,hz⟩ hz
    rwa [hermitian_support u v ⟨z,hz⟩] at he
  obtain ⟨t,ht,htb,hminor⟩ := bounded_nonzero_rows us vs hus hvs hms K hK
    (fun z => hpu z) (fun z => hpv z) hinds horths
  have hsum (f g : D → ℂ) (hf : ∀ z,u z=0 → f z=0) (N : ℕ) :
      powerPair (fun z : S => f z) (fun z : S => g z) N = powerPair f g N := by
    apply sum_support u (fun z => f z*g z^(N-1))
    intro z hz
    rw [hf z hz,zero_mul]
  have huu := hsum u u (fun _ h => h) (t*K)
  have huv := hsum u v (fun _ h => h) (t*K)
  have hvu := hsum v u (fun z h => (hzero z).mp h) (t*K)
  have hvv := hsum v v (fun z h => (hzero z).mp h) (t*K)
  refine ⟨t,ht,htb.trans (Fintype.card_subtype_le _),?_⟩
  simpa only [StrictMinor,us,vs,huu,huv,hvu,hvv] using hminor

/-- A strict principal magnitude minor contradicts the literal block-rank-one
condition, even for a nonsymmetric complex matrix. -/
theorem not_blockRankOne_of_minor {X : Type} (A : X → X → ℂ) (x y : X)
    (hxx : 0<‖A x x‖) (hxy : 0<‖A x y‖) (hyy : 0<‖A y y‖)
    (hdet : ‖A x y‖*‖A y x‖ < ‖A x x‖*‖A y y‖) : ¬BlockRankOne A := by
  intro hr
  have hx : A x≠0 := by intro hz; have := congrFun hz x; simp [this] at hxx
  have hy : A y≠0 := by intro hz; have := congrFun hz y; simp [this] at hyy
  rcases hr x y hx hy with ⟨c,hc,he⟩ | hd
  · rw [he x,he y] at hdet
    nlinarith
  · exact Set.disjoint_left.mp hd (norm_pos_iff.mp hxy) (norm_pos_iff.mp hyy)

/-- The full phase branch: literal non-BO with rank-one magnitudes and a common
phase exponent yields a bounded, actually generated two-power matrix whose
magnitudes fail block rank one. -/
theorem matrix_obstruction {X : Type} (G : X → D → ℂ)
    (hrank : BlockRankOne G) (hBO : ¬BlockOrthogonal G)
    (K : ℕ) (hK : 0<K) (hpow : ∀ x z,G x z^K=(‖G x z‖ : ℂ)^K) :
    ∃ t : ℕ, 0<t ∧ t ≤ Fintype.card D ∧
      ¬BlockRankOne (fun x y => powerPair (G x) (G y) (t*K)) := by
  have hp : ¬∀ x y, G x≠0 → G y≠0 → MagnitudeProportional (G x) (G y) →
      Proportional (G x) (G y) ∨ VectorBlockOrthogonal (G x) (G y) :=
    fun hp => hBO ⟨hrank,hp⟩
  push_neg at hp
  obtain ⟨x,y,hx,hy,hm,hi,ho⟩ := hp
  obtain ⟨t,ht,htb,hxx,hxy,hyy,hdet⟩ := bounded_rows (G x) (G y) hx hm K hK
    (hpow x) (hpow y) hi ho
  exact ⟨t,ht,htb,not_blockRankOne_of_minor _ x y hxx hxy hyy hdet⟩

end ComplexCSP.PhaseSupportObstruction
