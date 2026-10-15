module
public import Paper2.Certificates.DihedralSupport.SupportOrbitCheck00
public import Paper2.Certificates.DihedralSupport.SupportOrbitCheck01
public import Paper2.Certificates.DihedralSupport.SupportOrbitCheck02
public import Paper2.Certificates.DihedralSupport.SupportOrbitCheck03
public import Paper2.Certificates.DihedralSupport.SupportOrbitCheck04
public import Paper2.Certificates.DihedralSupport.SupportOrbitCheck05

/-! The exact signed-permutation orbit of the literal six-point support.
Finite witnesses give membership in one direction. Kernel-checked closure
under all bit flips and all transpositions gives the reverse direction. -/
@[expose] public section
namespace Paper2.Certificates.DihedralSupport.SupportOrbit

private theorem valid_all (i : Fin 480) : validAt i.val = true := by
  by_cases h0 : i.val < 80
  · exact checkRange_sound _ _ _ check_00 _ (by omega) (by omega)
  by_cases h1 : i.val < 160
  · exact checkRange_sound _ _ _ check_01 _ (by omega) (by omega)
  by_cases h2 : i.val < 240
  · exact checkRange_sound _ _ _ check_02 _ (by omega) (by omega)
  by_cases h3 : i.val < 320
  · exact checkRange_sound _ _ _ check_03 _ (by omega) (by omega)
  by_cases h4 : i.val < 400
  · exact checkRange_sound _ _ _ check_04 _ (by omega) (by omega)
  · exact checkRange_sound _ _ _ check_05 _ (by omega) (by omega)

private theorem row_valid (i : Fin 480) :
    actualMask i = maskAt i.val ∧
    (∀ p : Fin 15, swapNext i.val p < 480 ∧
      maskAction (Equiv.swap (pairPorts p).1 (pairPorts p).2) zeroWord (maskAt i.val) =
        maskAt (swapNext i.val p)) ∧
    (∀ j : Fin 6, flipNext i.val j < 480 ∧
      maskAction 1 (singleFlip j) (maskAt i.val) = maskAt (flipNext i.val j)) ∧
    (supportOfMask (maskAt i.val)).card = 6 ∧
    (∀ p : Fin 15, goodAt p (maskAt i.val) = true) ∧
    (∀ x : Word, (maskAt i.val).testBit (index6 x) = true →
      parity x = parity (word6 (Nat.log2 (maskAt i.val)))) := by
  simpa [validAt, i.isLt] using valid_all i

theorem actualMask_eq (i : Fin 480) : actualMask i = maskAt i.val := (row_valid i).1

noncomputable def orbitMasks : Finset Nat := Finset.univ.image actualMask

theorem orbitMasks_eq_data : orbitMasks = Finset.univ.image (fun i : Fin 480 => maskAt i.val) := by
  exact congrArg (fun f : Fin 480 → Nat => Finset.univ.image f) (funext actualMask_eq)

theorem data_mem (i : Fin 480) : maskAt i.val ∈ orbitMasks := by
  rw [orbitMasks_eq_data]
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

theorem mem_data {m : Nat} (hm : m ∈ orbitMasks) : ∃ i : Fin 480, maskAt i.val = m := by
  rw [orbitMasks_eq_data] at hm
  simpa using Finset.mem_image.mp hm

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
private theorem data_card : (Finset.univ.image (fun i : Fin 480 => maskAt i.val)).card = 480 := by
  decide +kernel

theorem orbitMasks_card : orbitMasks.card = 480 := by rw [orbitMasks_eq_data]; exact data_card

theorem orbit_lt {m : Nat} (hm : m ∈ orbitMasks) : m < 18446744073709551616 := by
  obtain ⟨i, rfl⟩ := mem_data hm
  exact maskAt_lt _

theorem orbit_support_card {m : Nat} (hm : m ∈ orbitMasks) : (supportOfMask m).card = 6 := by
  obtain ⟨i, rfl⟩ := mem_data hm
  exact (row_valid i).2.2.2.1

theorem orbit_good {m : Nat} (hm : m ∈ orbitMasks) (p : Fin 15) : goodAt p m = true := by
  obtain ⟨i, rfl⟩ := mem_data hm
  exact (row_valid i).2.2.2.2.1 p

theorem orbit_one_parity {m : Nat} (hm : m ∈ orbitMasks) :
    ∃ b : Bool, ∀ x : Word, m.testBit (index6 x) = true → parity x = b := by
  obtain ⟨i, rfl⟩ := mem_data hm
  exact ⟨_, (row_valid i).2.2.2.2.2⟩

theorem orbit_nonzero {m : Nat} (hm : m ∈ orbitMasks) : m ≠ 0 := by
  intro hz
  have hc := orbit_support_card hm
  simp [hz, supportOfMask] at hc

private theorem swap_generator_closed {m : Nat} (hm : m ∈ orbitMasks) (p : Fin 15) :
    maskAction (Equiv.swap (pairPorts p).1 (pairPorts p).2) zeroWord m ∈ orbitMasks := by
  obtain ⟨i, rfl⟩ := mem_data hm
  obtain ⟨hb, he⟩ := (row_valid i).2.1 p
  rw [he]
  exact data_mem ⟨swapNext i.val p, hb⟩

private theorem swap_closed {m : Nat} (hm : m ∈ orbitMasks) (i j : Fin 6) (hij : i ≠ j) :
    maskAction (Equiv.swap i j) zeroWord m ∈ orbitMasks := by
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · obtain ⟨p, hp⟩ := pairPorts_complete i j hlt
    simpa [hp] using swap_generator_closed hm p
  · obtain ⟨p, hp⟩ := pairPorts_complete j i hgt
    simpa [hp, Equiv.swap_comm] using swap_generator_closed hm p

private theorem perm_closed (σ : Equiv.Perm (Fin 6)) :
    ∀ m ∈ orbitMasks, maskAction σ zeroWord m ∈ orbitMasks := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one =>
    intro m hm
    simpa [maskAction_one m (orbit_lt hm)] using hm
  | swap_mul σ i j hij ih =>
    intro m hm
    rw [← maskAction_perm_comp]
    exact swap_closed (ih m hm) i j hij

private theorem singleFlip_closed {m : Nat} (hm : m ∈ orbitMasks) (j : Fin 6) :
    maskAction 1 (singleFlip j) m ∈ orbitMasks := by
  obtain ⟨i, rfl⟩ := mem_data hm
  obtain ⟨hb, he⟩ := (row_valid i).2.2.1 j
  rw [he]
  exact data_mem ⟨flipNext i.val j, hb⟩

private theorem flips_closed (s : Finset (Fin 6)) :
    ∀ m ∈ orbitMasks, maskAction 1 (flips s) m ∈ orbitMasks := by
  induction s using Finset.induction_on with
  | empty =>
    intro m hm
    have h : flips ∅ = zeroWord := by ext j; simp [flips, zeroWord]
    rw [h, maskAction_one m (orbit_lt hm)]
    exact hm
  | @insert j s hj ih =>
    intro m hm
    rw [maskAction_flips_insert j s hj]
    exact singleFlip_closed (ih m hm) j

private theorem flip_closed (b : Word) {m : Nat} (hm : m ∈ orbitMasks) :
    maskAction 1 b m ∈ orbitMasks := by
  let s := Finset.univ.filter fun i => b i = true
  have hb : flips s = b := by
    funext j
    cases hj : b j <;> simp [flips, s, hj]
  rw [← hb]
  exact flips_closed s m hm

theorem action_closed (σ : Equiv.Perm (Fin 6)) (b : Word) {m : Nat} (hm : m ∈ orbitMasks) :
    maskAction σ b m ∈ orbitMasks := by
  rw [← maskAction_perm_flip]
  exact perm_closed σ _ (flip_closed b hm)

theorem seed_mem : sstarMask ∈ orbitMasks := by rw [← maskAt_seed]; exact data_mem seedIndex

theorem mem_orbitMasks_iff (m : Nat) : m ∈ orbitMasks ↔
    ∃ σ : Equiv.Perm (Fin 6), ∃ b : Word, m = maskAction σ b sstarMask := by
  constructor
  · intro hm
    obtain ⟨i, hi, he⟩ := Finset.mem_image.mp hm
    exact ⟨perm i, word6 (flipAt i.val), he.symm⟩
  · rintro ⟨σ, b, rfl⟩
    exact action_closed σ b seed_mem

theorem support_orbit_iff (S : Word → Bool) : encodeSupport S ∈ orbitMasks ↔
    ∃ σ : Equiv.Perm (Fin 6), ∃ b : Word, ∀ x, S x = sstar (wordAction σ b x) := by
  rw [mem_orbitMasks_iff]
  constructor
  · rintro ⟨σ, b, he⟩
    refine ⟨σ, b, fun x => ?_⟩
    have hx := congrArg (fun m : Nat => m.testBit (index6 x)) he
    simpa [sstar] using hx
  · rintro ⟨σ, b, he⟩
    refine ⟨σ, b, ?_⟩
    unfold maskAction sstar at *
    congr 1
    exact funext he

theorem orbit_not_xorClosed {m : Nat} (hm : m ∈ orbitMasks) :
    ¬ XorClosed (fun x => m.testBit (index6 x)) := by
  obtain ⟨σ, b, rfl⟩ := (mem_orbitMasks_iff m).mp hm
  simpa [XorClosed, sstar] using signed_seed_not_xorClosed σ b

theorem support_not_xorClosed {S : Word → Bool} (hS : encodeSupport S ∈ orbitMasks) :
    ¬ XorClosed S := by
  simpa using orbit_not_xorClosed hS

end Paper2.Certificates.DihedralSupport.SupportOrbit
