import Paper2.Certificates.Q6CardNaturality

/-! The increasing order of a card's two external pairs is presentation only.
All legal unsorted cards reduce to the literal ordered-card hypothesis. -/
namespace Paper2.Certificates.Q6

def swapLeftCard (s : CardSpec) : CardSpec :=
  { s with left0 := s.left1, left1 := s.left0 }

def swapRightCard (s : CardSpec) : CardSpec :=
  { s with right0 := s.right1, right1 := s.right0 }

def swapLeftEntry : Equiv.Perm (Fin 6) where
  toFun := ![0,3,4,1,2,5]
  invFun := ![0,3,4,1,2,5]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

def swapRightEntry : Equiv.Perm (Fin 6) where
  toFun := ![0,2,1,4,3,5]
  invFun := ![0,2,1,4,3,5]
  left_inv i := by fin_cases i <;> rfl
  right_inv i := by fin_cases i <;> rfl

lemma swapLeftEntry_complement (e : Fin 6) :
    swapLeftEntry (entryComplement e) = entryComplement (swapLeftEntry e) := by
  fin_cases e <;> rfl
lemma swapRightEntry_complement (e : Fin 6) :
    swapRightEntry (entryComplement e) = entryComplement (swapRightEntry e) := by
  fin_cases e <;> rfl

lemma swapLeftCard_raw {s : CardSpec} (h : RawValidCardSpec s) :
    RawValidCardSpec (swapLeftCard s) := by
  refine ⟨Ne.symm h.1,h.2.1,h.2.2.1,?_⟩
  simpa only [internalLeft,internalRight,swapLeftCard,Finset.pair_comm] using h.2.2.2
lemma swapRightCard_raw {s : CardSpec} (h : RawValidCardSpec s) :
    RawValidCardSpec (swapRightCard s) := by
  refine ⟨h.1,Ne.symm h.2.1,h.2.2.1,?_⟩
  simpa only [internalLeft,internalRight,swapRightCard,Finset.pair_comm] using h.2.2.2

lemma internalChoices_swapLeft (s : CardSpec) (e : Fin 6) :
    internalChoices (swapLeftCard s) e = internalChoices s (swapLeftEntry e) := by
  have hi : internalLeft (swapLeftCard s) = internalLeft s := by
    exact congrArg (Finset.univ \ ·) (Finset.pair_comm _ _)
  unfold internalChoices
  rw [hi]
  have he : (eoWords e 0).toNat + (eoWords e 1).toNat =
      (eoWords (swapLeftEntry e) 0).toNat + (eoWords (swapLeftEntry e) 1).toNat := by
    fin_cases e <;> rfl
  rw [he]
lemma internalChoices_swapRight (s : CardSpec) (e : Fin 6) :
    internalChoices (swapRightCard s) e = internalChoices s (swapRightEntry e) := by
  fin_cases e <;> rfl

lemma selected_swap (u v : Port) (a b : Bool) :
    selected v u a b = selected u v b a := Finset.union_comm _ _

lemma swapLeftEntry_words (e : Fin 6) :
    eoWords (swapLeftEntry e) = ![eoWords e 1,eoWords e 0,eoWords e 2,eoWords e 3] := by
  fin_cases e <;> rfl
lemma swapRightEntry_words (e : Fin 6) :
    eoWords (swapRightEntry e) = ![eoWords e 0,eoWords e 1,eoWords e 3,eoWords e 2] := by
  fin_cases e <;> rfl

lemma sourceSets_swapLeft (s : CardSpec) (e : Fin 6) (T : PortSet) :
    sourceSets (swapLeftCard s) e T = sourceSets s (swapLeftEntry e) T := by
  unfold sourceSets
  rw [swapLeftEntry_words]
  change (selected s.left1 s.left0 (eoWords e 0) (eoWords e 1) ∪ T,
      selected s.right0 s.right1 (eoWords e 2) (eoWords e 3) ∪
        (internalRight s \ T.image s.wiring)) =
    (selected s.left0 s.left1 (eoWords e 1) (eoWords e 0) ∪ T,
      selected s.right0 s.right1 (eoWords e 2) (eoWords e 3) ∪
        (internalRight s \ T.image s.wiring))
  rw [selected_swap]
lemma sourceSets_swapRight (s : CardSpec) (e : Fin 6) (T : PortSet) :
    sourceSets (swapRightCard s) e T = sourceSets s (swapRightEntry e) T := by
  have hi : internalRight (swapRightCard s) = internalRight s := by
    exact congrArg (Finset.univ \ ·) (Finset.pair_comm _ _)
  unfold sourceSets
  rw [swapRightEntry_words,hi]
  change (selected s.left0 s.left1 (eoWords e 0) (eoWords e 1) ∪ T,
      selected s.right1 s.right0 (eoWords e 2) (eoWords e 3) ∪
        (internalRight s \ T.image s.wiring)) =
    (selected s.left0 s.left1 (eoWords e 0) (eoWords e 1) ∪ T,
      selected s.right0 s.right1 (eoWords e 3) (eoWords e 2) ∪
        (internalRight s \ T.image s.wiring))
  rw [selected_swap s.right0 s.right1 (eoWords e 2) (eoWords e 3)]

variable {K : Type*} [CommRing K]

lemma twoCopyArray_swapLeft (q : Fin 20 → K) (t : K) (s : CardSpec) :
    twoCopyArray q t (swapLeftCard s) = fun e => twoCopyArray q t s (swapLeftEntry e) := by
  funext e
  unfold twoCopyArray
  rw [internalChoices_swapLeft]
  simp only [sourceMasks,sourceSets_swapLeft]
  congr 1
  fin_cases e <;> rfl

lemma twoCopyArray_swapRight (q : Fin 20 → K) (t : K) (s : CardSpec) :
    twoCopyArray q t (swapRightCard s) = fun e => twoCopyArray q t s (swapRightEntry e) := by
  funext e
  unfold twoCopyArray
  rw [internalChoices_swapRight]
  simp only [sourceMasks,sourceSets_swapRight]
  congr 1
  fin_cases e <;> rfl

variable [NoZeroDivisors K]

lemma NecessarySafe.swapLeftCard {q : Fin 20 → K} {t : K} {s : CardSpec}
    (h : NecessarySafe (twoCopyArray q t (swapLeftCard s))) :
    NecessarySafe (twoCopyArray q t s) := by
  have ht := h.reindex swapLeftEntry swapLeftEntry_complement
  rw [twoCopyArray_swapLeft] at ht
  have hh : (fun i => twoCopyArray q t s (swapLeftEntry (swapLeftEntry i))) = twoCopyArray q t s := by
    funext i
    fin_cases i <;> rfl
  rwa [hh] at ht

lemma NecessarySafe.swapRightCard {q : Fin 20 → K} {t : K} {s : CardSpec}
    (h : NecessarySafe (twoCopyArray q t (swapRightCard s))) :
    NecessarySafe (twoCopyArray q t s) := by
  have ht := h.reindex swapRightEntry swapRightEntry_complement
  rw [twoCopyArray_swapRight] at ht
  have hh : (fun i => twoCopyArray q t s (swapRightEntry (swapRightEntry i))) = twoCopyArray q t s := by
    funext i
    fin_cases i <;> rfl
  rwa [hh] at ht

/-- All physically legal four-wire cards, without requiring a convention on
which of the two external ports is named first. -/
theorem AllTwoCopySafe.of_raw (q : Fin 20 → K) (t : K) (h : AllTwoCopySafe q t)
    (s : CardSpec) (hs : RawValidCardSpec s) : NecessarySafe (twoCopyArray q t s) := by
  by_cases hl : s.left0 < s.left1
  · by_cases hr : s.right0 < s.right1
    · exact h s ⟨hl,hr,hs.2.2⟩
    · apply NecessarySafe.swapRightCard
      exact h (swapRightCard s) ⟨hl,lt_of_le_of_ne (le_of_not_gt hr) hs.2.1.symm,
        (swapRightCard_raw hs).2.2⟩
  · have hl' : s.left1 < s.left0 := lt_of_le_of_ne (le_of_not_gt hl) hs.1.symm
    apply NecessarySafe.swapLeftCard
    by_cases hr : s.right0 < s.right1
    · exact h (swapLeftCard s) ⟨hl',hr,(swapLeftCard_raw hs).2.2⟩
    · apply NecessarySafe.swapRightCard
      exact h (swapRightCard (swapLeftCard s))
        ⟨hl',lt_of_le_of_ne (le_of_not_gt hr) hs.2.1.symm,
          (swapRightCard_raw (swapLeftCard_raw hs)).2.2⟩

end Paper2.Certificates.Q6
