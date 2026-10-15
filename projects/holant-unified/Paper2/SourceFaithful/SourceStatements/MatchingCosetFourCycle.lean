import Holant.Dihedral.EndpointParallelogram.Matching
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! The arbitrary-port matching geometry used by manuscript Lemma 5.15.
A half-size intersection of two distinct binary matching codes forces exactly
one alternating four-cycle; every other literal matched edge is unchanged. -/
namespace Paper2.SourceFaithful.SourceStatements
noncomputable section
open Holant.Dihedral.EndpointParallelogram

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The literal finite set of words in a perfect matching's binary code. -/
def matchingCodeSet (M : Pairing ι) : Finset (ι → ZMod 2) :=
  by classical exact Finset.univ.filter (fun x => x ∈ M.code)

@[simp] theorem mem_matchingCodeSet (M : Pairing ι) (x : ι → ZMod 2) :
    x ∈ matchingCodeSet M ↔ x ∈ M.code := by
  simp [matchingCodeSet]

private theorem flip_eq_iff (u v : ZMod 2) : u+1 = v ↔ u ≠ v := by
  fin_cases u <;> fin_cases v
  · change (0 : ZMod 2)+1 = 0 ↔ (0 : ZMod 2) ≠ 0
    decide
  · change (0 : ZMod 2)+1 = 1 ↔ (0 : ZMod 2) ≠ 1
    decide
  · change (1 : ZMod 2)+1 = 0 ↔ (1 : ZMod 2) ≠ 0
    decide
  · change (1 : ZMod 2)+1 = 1 ↔ (1 : ZMod 2) ≠ 1
    decide

omit [Fintype ι] [DecidableEq ι] in
private theorem toggle_twice (w x : ι → ZMod 2) : (x+w)+w = x := by
  rw [add_assoc,ZModModule.add_self,add_zero]

/-- Equating bits on two different matched edges cuts a matching code exactly
in half. The proof toggles one actual matched edge, in arbitrary port arity. -/
theorem matching_code_hyperplane_half (M : Pairing ι) (a c : ι)
    (hca : c ≠ a) (hcb : c ≠ M.mate a) :
    2 * ((matchingCodeSet M).filter (fun x => x a = x c)).card =
      (matchingCodeSet M).card := by
  classical
  let w := M.edgeWord a
  let τ := fun x : ι → ZMod 2 => x+w
  have hw : w ∈ M.code := M.edgeWord_mem a
  have hwa : w a = 1 := by simp [w,Pairing.edgeWord]
  have hwc : w c = 0 := by simp [w,Pairing.edgeWord,hca,hcb]
  have ht : Function.Involutive τ := toggle_twice w
  have hm (x : ι → ZMod 2) : τ x ∈ M.code ↔ x ∈ M.code := by
    constructor
    · intro h
      simpa only [τ,toggle_twice] using M.code.add_mem h hw
    · intro h
      exact M.code.add_mem h hw
  have hp (x : ι → ZMod 2) : (τ x) a = (τ x) c ↔ x a ≠ x c := by
    simp only [τ,Pi.add_apply,hwa,hwc,add_zero,flip_eq_iff]
  have hcards : ((matchingCodeSet M).filter (fun x => x a = x c)).card =
      ((matchingCodeSet M).filter (fun x => ¬ x a = x c)).card := by
    apply Finset.card_bijective τ ht.bijective
    intro x
    simp only [Finset.mem_filter,mem_matchingCodeSet,hm,hp,not_not]
  have hpartition := Finset.card_filter_add_card_filter_not
    (s := matchingCodeSet M) (fun x => x a = x c)
  omega

/-- If the intersection has exactly half the size of one matching code, its
single equality on any changed edge already characterizes the intersection. -/
theorem matching_code_intersection_hyperplane (M N : Pairing ι) (a : ι)
    (hdiff : N.mate a ≠ M.mate a)
    (hhalf : 2 * (matchingCodeSet M ∩ matchingCodeSet N).card =
      (matchingCodeSet M).card) :
    matchingCodeSet M ∩ matchingCodeSet N =
      (matchingCodeSet M).filter (fun x => x a = x (N.mate a)) := by
  classical
  have hsub : matchingCodeSet M ∩ matchingCodeSet N ⊆
      (matchingCodeSet M).filter (fun x => x a = x (N.mate a)) := by
    intro x hx
    obtain ⟨hxM,hxN⟩ := Finset.mem_inter.mp hx
    exact Finset.mem_filter.mpr ⟨hxM,((mem_matchingCodeSet N x).mp hxN a).symm⟩
  have hh := matching_code_hyperplane_half M a (N.mate a) (N.fixed_free a) hdiff
  apply Finset.eq_of_subset_of_card_le hsub
  omega

/-- The matching difference is supported on four distinct original ports.
The first matching uses `a-b,c-d`, the second `a-c,b-d`, and all other matched
edges are literally equal, without a supplied cycle decomposition. -/
structure SingleFourCycle (M N : Pairing ι) where
  a : ι
  b : ι
  c : ι
  d : ι
  ab : a ≠ b
  ac : a ≠ c
  ad : a ≠ d
  bc : b ≠ c
  bd : b ≠ d
  cd : c ≠ d
  first_ab : M.mate a = b
  first_cd : M.mate c = d
  second_ac : N.mate a = c
  second_bd : N.mate b = d
  outside : ∀ i, i ≠ a → i ≠ b → i ≠ c → i ≠ d → N.mate i = M.mate i

/-- A half-size intersection of distinct binary matching codes forces one
alternating four-cycle, for arbitrary finite original port type. -/
theorem matching_codes_single_four_cycle (M N : Pairing ι) (hne : M ≠ N)
    (hhalf : 2 * (matchingCodeSet M ∩ matchingCodeSet N).card =
      (matchingCodeSet M).card) : Nonempty (SingleFourCycle M N) := by
  classical
  have hex : ∃ a, N.mate a ≠ M.mate a := by
    by_contra h
    push Not at h
    exact hne (Pairing.ext (funext fun i => (h i).symm))
  obtain ⟨a,ha⟩ := hex
  let b := M.mate a
  let c := N.mate a
  let d := M.mate c
  have hba : b ≠ a := M.fixed_free a
  have hca : c ≠ a := N.fixed_free a
  have hcb : c ≠ b := ha
  have hdc : d ≠ c := M.fixed_free c
  have hda : d ≠ a := by
    intro h
    have hh := congrArg M.mate h
    exact hcb (by simpa only [d,M.involutive c] using hh)
  have hdb : d ≠ b := by
    intro h
    have hh := congrArg M.mate h
    exact hca (by simpa only [d,b,M.involutive c,M.involutive a] using hh)
  have hinter := matching_code_intersection_hyperplane M N a ha hhalf
  have hout (i : ι) (hia : i ≠ a) (hib : i ≠ b) (hic : i ≠ c) (hid : i ≠ d) :
      N.mate i = M.mate i := by
    have haw : M.edgeWord i a = 0 := by
      have hai : a ≠ i := Ne.symm hia
      have ham : a ≠ M.mate i := by
        intro h
        exact hib (by simpa only [M.involutive i,b] using congrArg M.mate h.symm)
      simp [Pairing.edgeWord,hai,ham]
    have hcw : M.edgeWord i c = 0 := by
      have hci : c ≠ i := Ne.symm hic
      have hcm : c ≠ M.mate i := by
        intro h
        exact hid (by simpa only [M.involutive i,d] using congrArg M.mate h.symm)
      simp [Pairing.edgeWord,hci,hcm]
    have hiH : M.edgeWord i ∈ (matchingCodeSet M).filter
        (fun x => x a = x (N.mate a)) := by
      exact Finset.mem_filter.mpr ⟨(mem_matchingCodeSet M _).mpr (M.edgeWord_mem i),
        by change M.edgeWord i a = M.edgeWord i c; rw [haw,hcw]⟩
    rw [← hinter] at hiH
    have hiN := (mem_matchingCodeSet N _).mp (Finset.mem_inter.mp hiH).2
    have hh := hiN i
    have hwi : M.edgeWord i i = 1 := by simp [Pairing.edgeWord]
    rw [hwi] at hh
    have hi : N.mate i = i ∨ N.mate i = M.mate i := by
      by_contra hn
      simp [Pairing.edgeWord,hn] at hh
    exact hi.resolve_left (N.fixed_free i)
  have hNb : N.mate b = d := by
    by_contra hnebd
    have hk_a : N.mate b ≠ a := by
      intro h
      exact hcb (by simpa only [N.involutive b,c] using congrArg N.mate h.symm)
    have hk_b : N.mate b ≠ b := N.fixed_free b
    have hk_c : N.mate b ≠ c := by
      intro h
      exact hba (by simpa only [c,N.involutive b,N.involutive a] using congrArg N.mate h)
    have hh := hout (N.mate b) hk_a hk_b hk_c hnebd
    have hk : N.mate b = a := by
      have h := congrArg M.mate hh
      simpa only [N.involutive b,M.involutive (N.mate b),b,M.involutive a] using h.symm
    exact hk_a hk
  exact ⟨⟨a,b,c,d,Ne.symm hba,Ne.symm hca,Ne.symm hda,
    Ne.symm hcb,Ne.symm hdb,Ne.symm hdc,rfl,rfl,rfl,hNb,hout⟩⟩

/- Recenter both actual affine supports at an actual common word. -/
omit [Fintype ι] [DecidableEq ι] in
theorem binary_coset_recenter (L : Submodule (ZMod 2) (ι → ZMod 2))
    (offset c x : ι → ZMod 2) (hc : c+offset ∈ L) :
    x+offset ∈ L ↔ x+c ∈ L := by
  have hcancel (u v : ι → ZMod 2) : u+v+v = u := toggle_twice v u
  constructor
  · intro hx
    have h := L.add_mem hx hc
    have he : (x+offset)+(c+offset) = x+c := by
      calc
        _ = (x+c)+offset+offset := by abel
        _ = _ := hcancel _ _
    rwa [he] at h
  · intro hx
    have h := L.add_mem hx hc
    have he : (x+c)+(c+offset) = x+offset := by
      calc
        _ = (x+offset)+c+c := by abel
        _ = _ := hcancel _ _
    rwa [he] at h

/-- The same four-cycle conclusion for actual affine matching supports. Their
offsets may differ; a common supported word determines a literal translation
to the direction-code theorem. Distinctness of the pairings is derived. -/
theorem matching_cosets_single_four_cycle (M N : Pairing ι)
    (S T : Finset (ι → ZMod 2)) (offsetM offsetN : ι → ZMod 2)
    (hS : ∀ x, x ∈ S ↔ x+offsetM ∈ M.code)
    (hT : ∀ x, x ∈ T ↔ x+offsetN ∈ N.code)
    (hne : S ≠ T) (hcommon : (S ∩ T).Nonempty)
    (hhalf : 2 * (S ∩ T).card = S.card) : Nonempty (SingleFourCycle M N) := by
  classical
  obtain ⟨c,hc⟩ := hcommon
  obtain ⟨hcS,hcT⟩ := Finset.mem_inter.mp hc
  have hMc := (hS c).mp hcS
  have hNc := (hT c).mp hcT
  let τ := fun x : ι → ZMod 2 => x+c
  have hτ : Function.Involutive τ := toggle_twice c
  have hSM (x : ι → ZMod 2) : x ∈ S ↔ τ x ∈ M.code :=
    (hS x).trans (binary_coset_recenter M.code offsetM c x hMc)
  have hTN (x : ι → ZMod 2) : x ∈ T ↔ τ x ∈ N.code :=
    (hT x).trans (binary_coset_recenter N.code offsetN c x hNc)
  have hMN : M ≠ N := by
    intro heq
    apply hne
    ext x
    rw [hSM,hTN,heq]
  have hcardS : S.card = (matchingCodeSet M).card := by
    apply Finset.card_bijective τ hτ.bijective
    intro x
    exact (hSM x).trans (mem_matchingCodeSet M (τ x)).symm
  have hcardI : (S ∩ T).card = (matchingCodeSet M ∩ matchingCodeSet N).card := by
    apply Finset.card_bijective τ hτ.bijective
    intro x
    simp only [Finset.mem_inter,mem_matchingCodeSet,hSM,hTN]
  apply matching_codes_single_four_cycle M N hMN
  rw [← hcardI,← hcardS]
  exact hhalf

omit [Fintype ι] [DecidableEq ι] in
/-- Translation by a direction word preserves the actual affine support. -/
theorem matching_coset_translate (M : Pairing ι) (S : Finset (ι → ZMod 2))
    (offset : ι → ZMod 2) (hS : ∀ x, x ∈ S ↔ x+offset ∈ M.code)
    (w : ι → ZMod 2) (hw : w ∈ M.code) (x : ι → ZMod 2) :
    x+w ∈ S ↔ x ∈ S := by
  rw [hS,hS,show (x+w)+offset = (x+offset)+w by abel]
  constructor
  · intro h
    simpa only [toggle_twice] using M.code.add_mem h hw
  · intro h
    exact M.code.add_mem h hw

omit [DecidableEq ι] in
/-- Every direction shared by two affine matching supports remains a direction
of a nonempty matching support equal to their symmetric difference. -/
theorem symmetric_difference_common_code (M N P : Pairing ι)
    (S T U : Finset (ι → ZMod 2)) (oM oN oP : ι → ZMod 2)
    (hS : ∀ x, x ∈ S ↔ x+oM ∈ M.code)
    (hT : ∀ x, x ∈ T ↔ x+oN ∈ N.code)
    (hU : ∀ x, x ∈ U ↔ x+oP ∈ P.code)
    (hshape : U = (S \ T) ∪ (T \ S)) (hUne : U.Nonempty)
    (w : ι → ZMod 2) (hwM : w ∈ M.code) (hwN : w ∈ N.code) : w ∈ P.code := by
  obtain ⟨x,hx⟩ := hUne
  have hxw : x+w ∈ U := by
    rw [hshape] at hx ⊢
    simpa only [Finset.mem_union,Finset.mem_sdiff,
      matching_coset_translate M S oM hS w hwM,
      matching_coset_translate N T oN hT w hwN] using hx
  have h := P.code.add_mem ((hU x).mp hx) ((hU (x+w)).mp hxw)
  have he : (x+oP)+((x+w)+oP) = w := by
    calc
      _ = (w+(x+x))+(oP+oP) := by abel
      _ = w := by rw [ZModModule.add_self,ZModModule.add_self,add_zero,add_zero]
  rwa [he] at h

omit [Fintype ι] in
/-- The indicator of a literal edge recovers the edge in every matching code
that contains it. -/
theorem matching_edge_of_word (M P : Pairing ι) (i : ι)
    (hi : M.edgeWord i ∈ P.code) : P.mate i = M.mate i := by
  classical
  have hh := hi i
  have hwi : M.edgeWord i i = 1 := by simp [Pairing.edgeWord]
  rw [hwi] at hh
  have h : P.mate i = i ∨ P.mate i = M.mate i := by
    by_contra hn
    simp [Pairing.edgeWord,hn] at hh
  exact h.resolve_left (P.fixed_free i)

/-- All three perfect matchings agree outside one four-port cycle and use its
three different pairings. -/
structure ThreePairingsFourCycle (M N P : Pairing ι) extends SingleFourCycle M N where
  third_ad : P.mate a = d
  third_bc : P.mate b = c
  third_outside : ∀ i, i ≠ a → i ≠ b → i ≠ c → i ≠ d → P.mate i = M.mate i

omit [Fintype ι] [DecidableEq ι] in
/-- A third matching with the same outside edges and distinct from both
original matchings must use the remaining pairing of the four ports. -/
def third_pairing_of_common_outside (M N P : Pairing ι)
    (C : SingleFourCycle M N) (hPM : P ≠ M) (hPN : P ≠ N)
    (hout : ∀ i, i ≠ C.a → i ≠ C.b → i ≠ C.c → i ≠ C.d →
      P.mate i = M.mate i) : ThreePairingsFourCycle M N P := by
  classical
  have hba : M.mate C.b = C.a := by
    rw [← C.first_ab,M.involutive C.a]
  have hdc : M.mate C.d = C.c := by
    rw [← C.first_cd,M.involutive C.c]
  have hca : N.mate C.c = C.a := by
    rw [← C.second_ac,N.involutive C.a]
  have hdb : N.mate C.d = C.b := by
    rw [← C.second_bd,N.involutive C.b]
  have hfour (i : ι) (hi : i = C.a ∨ i = C.b ∨ i = C.c ∨ i = C.d) :
      P.mate i = C.a ∨ P.mate i = C.b ∨ P.mate i = C.c ∨ P.mate i = C.d := by
    by_contra h
    push Not at h
    obtain ⟨ha,hb,hc,hd⟩ := h
    have hh := hout (P.mate i) ha hb hc hd
    rw [P.involutive i] at hh
    have hm : P.mate i = M.mate i := by
      have h := congrArg M.mate hh
      rw [M.involutive (P.mate i)] at h
      exact h.symm
    rcases hi with rfl | rfl | rfl | rfl
    · exact hb (hm.trans C.first_ab)
    · exact ha (hm.trans hba)
    · exact hd (hm.trans C.first_cd)
    · exact hc (hm.trans hdc)
  have hadd : P.mate C.a = C.d := by
    obtain ha | hb | hc | hd := hfour C.a (Or.inl rfl)
    · exact False.elim (P.fixed_free C.a ha)
    · have hPaB : P.mate C.b = C.a := by rw [← hb,P.involutive C.a]
      have hPcD : P.mate C.c = C.d := by
        obtain hca' | hcb' | hcc' | hcd' := hfour C.c (Or.inr (Or.inr (Or.inl rfl)))
        · have h := congrArg P.mate hca'
          rw [P.involutive C.c,hb] at h
          exact False.elim (C.bc h.symm)
        · have h := congrArg P.mate hcb'
          rw [P.involutive C.c,hPaB] at h
          exact False.elim (C.ac h.symm)
        · exact False.elim (P.fixed_free C.c hcc')
        · exact hcd'
      have hPdC : P.mate C.d = C.c := by rw [← hPcD,P.involutive C.c]
      apply False.elim
      apply hPM
      apply Pairing.ext
      funext i
      by_cases ha : i = C.a
      · subst i; exact hb.trans C.first_ab.symm
      by_cases hb' : i = C.b
      · subst i; exact hPaB.trans hba.symm
      by_cases hc' : i = C.c
      · subst i; exact hPcD.trans C.first_cd.symm
      by_cases hd' : i = C.d
      · subst i; exact hPdC.trans hdc.symm
      exact hout i ha hb' hc' hd'
    · have hPcA : P.mate C.c = C.a := by rw [← hc,P.involutive C.a]
      have hPbD : P.mate C.b = C.d := by
        obtain hba' | hbb' | hbc' | hbd' := hfour C.b (Or.inr (Or.inl rfl))
        · have h := congrArg P.mate hba'
          rw [P.involutive C.b,hc] at h
          exact False.elim (C.bc h)
        · exact False.elim (P.fixed_free C.b hbb')
        · have h := congrArg P.mate hbc'
          rw [P.involutive C.b,hPcA] at h
          exact False.elim (C.ab h.symm)
        · exact hbd'
      have hPdB : P.mate C.d = C.b := by rw [← hPbD,P.involutive C.b]
      apply False.elim
      apply hPN
      apply Pairing.ext
      funext i
      by_cases ha : i = C.a
      · subst i; exact hc.trans C.second_ac.symm
      by_cases hb' : i = C.b
      · subst i; exact hPbD.trans C.second_bd.symm
      by_cases hc' : i = C.c
      · subst i; exact hPcA.trans hca.symm
      by_cases hd' : i = C.d
      · subst i; exact hPdB.trans hdb.symm
      exact (hout i ha hb' hc' hd').trans (C.outside i ha hb' hc' hd').symm
    · exact hd
  have hPdA : P.mate C.d = C.a := by rw [← hadd,P.involutive C.a]
  have hbc : P.mate C.b = C.c := by
    obtain hba' | hbb' | hbc' | hbd' := hfour C.b (Or.inr (Or.inl rfl))
    · have h := congrArg P.mate hba'
      rw [P.involutive C.b,hadd] at h
      exact False.elim (C.bd h)
    · exact False.elim (P.fixed_free C.b hbb')
    · exact hbc'
    · have h := congrArg P.mate hbd'
      rw [P.involutive C.b,hPdA] at h
      exact False.elim (C.ab h.symm)
  exact ⟨C,hadd,hbc,hout⟩

omit [DecidableEq ι] in
/-- Distinct affine matching supports that meet have distinct pairings. -/
theorem matching_cosets_pairing_ne (M N : Pairing ι)
    (S T : Finset (ι → ZMod 2)) (oM oN : ι → ZMod 2)
    (hS : ∀ x, x ∈ S ↔ x+oM ∈ M.code)
    (hT : ∀ x, x ∈ T ↔ x+oN ∈ N.code)
    (hne : S ≠ T) (hcommon : (S ∩ T).Nonempty) : M ≠ N := by
  obtain ⟨c,hc⟩ := hcommon
  obtain ⟨hcS,hcT⟩ := Finset.mem_inter.mp hc
  have hMc := (hS c).mp hcS
  have hNc := (hT c).mp hcT
  intro heq
  apply hne
  ext x
  rw [hS,hT,binary_coset_recenter M.code oM c x hMc,
    binary_coset_recenter N.code oN c x hNc,heq]

/-- The complete arbitrary-port support geometry of the different-support
branch of Lemma 5.15: three actual matching cosets of equal size, with the third
equal to the symmetric difference and the first two meeting in half their
size, use precisely the three pairings of one four-port cycle. -/
theorem three_matching_cosets_four_cycle (M N P : Pairing ι)
    (S T U : Finset (ι → ZMod 2)) (oM oN oP : ι → ZMod 2)
    (hS : ∀ x, x ∈ S ↔ x+oM ∈ M.code)
    (hT : ∀ x, x ∈ T ↔ x+oN ∈ N.code)
    (hU : ∀ x, x ∈ U ↔ x+oP ∈ P.code)
    (hne : S ≠ T) (hcommon : (S ∩ T).Nonempty)
    (hhalf : 2 * (S ∩ T).card = S.card) (hcard : S.card = T.card)
    (hshape : U = (S \ T) ∪ (T \ S)) :
    Nonempty (ThreePairingsFourCycle M N P) := by
  classical
  obtain ⟨C⟩ := matching_cosets_single_four_cycle M N S T oM oN hS hT hne hcommon hhalf
  have hexS : (S \ T).Nonempty := by
    apply Finset.sdiff_nonempty.mpr
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega))
  have hexT : (T \ S).Nonempty := by
    apply Finset.sdiff_nonempty.mpr
    intro hsub
    exact hne (Finset.eq_of_subset_of_card_le hsub (by omega)).symm
  have hSU : S ≠ U := by
    intro heq
    obtain ⟨x,hx⟩ := hcommon
    obtain ⟨hxS,hxT⟩ := Finset.mem_inter.mp hx
    have hxU : x ∈ U := heq ▸ hxS
    rw [hshape] at hxU
    simp only [Finset.mem_union,Finset.mem_sdiff] at hxU
    exact hxU.elim (fun h => h.2 hxT) (fun h => h.2 hxS)
  have hTU : T ≠ U := by
    intro heq
    obtain ⟨x,hx⟩ := hcommon
    obtain ⟨hxS,hxT⟩ := Finset.mem_inter.mp hx
    have hxU : x ∈ U := heq ▸ hxT
    rw [hshape] at hxU
    simp only [Finset.mem_union,Finset.mem_sdiff] at hxU
    exact hxU.elim (fun h => h.2 hxT) (fun h => h.2 hxS)
  have hSUcommon : (S ∩ U).Nonempty := by
    obtain ⟨x,hx⟩ := hexS
    exact ⟨x,Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hx).1,
      hshape ▸ Finset.mem_union.mpr (Or.inl hx)⟩⟩
  have hTUcommon : (T ∩ U).Nonempty := by
    obtain ⟨x,hx⟩ := hexT
    exact ⟨x,Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hx).1,
      hshape ▸ Finset.mem_union.mpr (Or.inr hx)⟩⟩
  have hUne : U.Nonempty := Finset.Nonempty.mono Finset.inter_subset_right hSUcommon
  have hPM : P ≠ M := Ne.symm (matching_cosets_pairing_ne M P S U oM oP hS hU hSU hSUcommon)
  have hPN : P ≠ N := Ne.symm (matching_cosets_pairing_ne N P T U oN oP hT hU hTU hTUcommon)
  have hout (i : ι) (ha : i ≠ C.a) (hb : i ≠ C.b) (hc : i ≠ C.c) (hd : i ≠ C.d) :
      P.mate i = M.mate i := by
    have hword : M.edgeWord i = N.edgeWord i := by
      funext j
      simp only [Pairing.edgeWord,C.outside i ha hb hc hd]
    have hwN : M.edgeWord i ∈ N.code := hword ▸ N.edgeWord_mem i
    apply matching_edge_of_word M P i
    exact symmetric_difference_common_code M N P S T U oM oN oP hS hT hU
      hshape hUne (M.edgeWord i) (M.edgeWord_mem i) hwN
  exact ⟨third_pairing_of_common_outside M N P C hPM hPN hout⟩

end
end Paper2.SourceFaithful.SourceStatements

