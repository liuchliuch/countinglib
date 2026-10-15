import Paper2.Certificates.Q6CardOrder

/-! Reversing all six source bits relabels the summation subset by its
complement in the four internal ports. This is an exact finite-sum identity. -/
namespace Paper2.Certificates.Q6

lemma internalLeft_card (s : CardSpec) (hs : RawValidCardSpec s) :
    (internalLeft s).card = 4 := by
  rw [internalLeft, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_pair hs.1]
  rfl

lemma choice_subset {s : CardSpec} {e : Fin 6} {T : PortSet}
    (h : T ∈ internalChoices s e) : T ⊆ internalLeft s :=
  Finset.mem_powerset.mp (Finset.mem_filter.mp h).1

lemma choice_complement_mem (s : CardSpec) (hs : RawValidCardSpec s)
    (e : Fin 6) (T : PortSet) (hT : T ∈ internalChoices s e) :
    internalLeft s \ T ∈ internalChoices s (entryComplement e) := by
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset,?_⟩
  rw [Finset.card_sdiff_of_subset (choice_subset hT),internalLeft_card s hs]
  have hc := (Finset.mem_filter.mp hT).2
  rw [hc]
  fin_cases e <;> rfl

lemma internalChoices_complement (s : CardSpec) (hs : RawValidCardSpec s) (e : Fin 6) :
    internalChoices s (entryComplement e) =
      (internalChoices s e).image (fun T => internalLeft s \ T) := by
  ext T
  constructor
  · intro ht
    refine Finset.mem_image.mpr ⟨internalLeft s \ T,?_,?_⟩
    · have hh := choice_complement_mem s hs (entryComplement e) T ht
      have he : entryComplement (entryComplement e) = e := by fin_cases e <;> rfl
      rwa [he] at hh
    · exact Finset.sdiff_sdiff_eq_self (choice_subset ht)
  · intro ht
    obtain ⟨U,hU,rfl⟩ := Finset.mem_image.mp ht
    exact choice_complement_mem s hs e U hU

lemma selected_union_complement (u v : Port) (huv : u ≠ v) (a b : Bool)
    (T : PortSet) (hT : T ⊆ Finset.univ \ {u,v}) :
    Finset.univ \ (selected u v a b ∪ T) =
      selected u v (!a) (!b) ∪ ((Finset.univ \ {u,v}) \ T) := by
  ext x
  have hx : x ∈ T → x ≠ u ∧ x ≠ v := by
    intro ht
    simpa only [Finset.mem_sdiff,Finset.mem_univ,Finset.mem_insert,
      Finset.mem_singleton,true_and,not_or] using hT ht
  cases a <;> cases b <;>
    simp only [selected,Bool.not_false,Bool.not_true,Bool.false_eq_true,
      if_false,if_true,Finset.empty_union,Finset.union_empty,
      Finset.mem_sdiff,Finset.mem_univ,Finset.mem_union,Finset.mem_singleton,
      Finset.mem_insert,Finset.notMem_empty,true_and,not_or]
  all_goals by_cases hu : x = u <;> by_cases hv : x = v <;> aesop

lemma sourceSets_complement (s : CardSpec) (hs : RawValidCardSpec s)
    (e : Fin 6) (T : PortSet) (hT : T ⊆ internalLeft s) :
    sourceSets s (entryComplement e) (internalLeft s \ T) =
      (Finset.univ \ (sourceSets s e T).1, Finset.univ \ (sourceSets s e T).2) := by
  have him : T.image s.wiring ⊆ internalRight s := by
    rw [← hs.2.2.2]
    exact Finset.image_subset_image hT
  have hw : (internalLeft s \ T).image s.wiring = internalRight s \ T.image s.wiring := by
    rw [Finset.image_sdiff _ _ hs.2.2.1.1,hs.2.2.2]
  have bits (j : Fin 4) : eoWords (entryComplement e) j = !(eoWords e j) := by
    fin_cases e <;> fin_cases j <;> rfl
  have hl : Finset.univ \ (sourceSets s e T).1 =
      selected s.left0 s.left1 (!(eoWords e 0)) (!(eoWords e 1)) ∪ (internalLeft s \ T) :=
    selected_union_complement s.left0 s.left1 hs.1 _ _ T hT
  have hr : Finset.univ \ (sourceSets s e T).2 =
      selected s.right0 s.right1 (!(eoWords e 2)) (!(eoWords e 3)) ∪
        (internalRight s \ (internalRight s \ T.image s.wiring)) :=
    selected_union_complement s.right0 s.right1 hs.2.1 _ _
      (internalRight s \ T.image s.wiring) Finset.sdiff_subset
  rw [hl,hr]
  unfold sourceSets
  simp only [bits,hw]

variable {K : Type*} [CommRing K]

lemma twoCopyArray_complement (q q' : Fin 20 → K) (t : K)
    (s : CardSpec) (hs : RawValidCardSpec s)
    (hq : ∀ S : PortSet, coefficient q' (mask S) = coefficient q (mask (Finset.univ \ S))) :
    twoCopyArray q' t s = fun e => twoCopyArray q t s (entryComplement e) := by
  funext e
  unfold twoCopyArray
  rw [internalChoices_complement s hs e,Finset.sum_image]
  · have hend : (if e = 0 ∨ e = 5 then t else 0) =
        (if entryComplement e = 0 ∨ entryComplement e = 5 then t else 0) := by
      fin_cases e <;> rfl
    rw [hend]
    congr 1
    apply Finset.sum_congr rfl
    intro T hT
    simp only [sourceMasks,sourceSets_complement s hs e T (choice_subset hT),hq]
  · intro T hT U hU he
    have hh := congrArg (fun S => internalLeft s \ S) he
    simpa only [Finset.sdiff_sdiff_eq_self (choice_subset hT),
      Finset.sdiff_sdiff_eq_self (choice_subset hU)] using hh

end Paper2.Certificates.Q6
