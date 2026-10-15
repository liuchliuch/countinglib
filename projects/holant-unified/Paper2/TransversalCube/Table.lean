import Paper2.TransversalCube.Path

namespace Paper2.TransversalCube
open scoped BigOperators
noncomputable section
variable {K : Type*} [CommRing K] [IsDomain K] {m : ℕ}

def central (p q : Fin (m+1) → K) (c : K) (w : Ports m → Bool) : K :=
  c * ∏ j, WeightedMatching.binary (p j) (q j) (w (j,false)) (w (j,true))

def mountain (a b c : K) (p q : Fin (m+1) → K) (w : Ports m → Bool) : K :=
  (if w = (fun _ => false) then a else 0) +
    (if w = (fun _ => true) then b else 0) + central p q c w

lemma central_ne_zero (p q : Fin (m+1) → K) (c : K)
    (h : c * ∏ j, p j * q j ≠ 0) (w : Ports m → Bool) :
    central p q c w ≠ 0 ↔ Opposite w := by
  have hc : c ≠ 0 := left_ne_zero_of_mul h
  have hpq : ∀ j, p j ≠ 0 ∧ q j ≠ 0 := by
    simpa [Finset.prod_ne_zero_iff] using right_ne_zero_of_mul h
  simp [central, hc, Finset.prod_ne_zero_iff,
    WeightedMatching.binary_ne_zero (hpq _).1 (hpq _).2, Opposite]

@[simp] lemma central_constant (p q : Fin (m+1) → K) (c : K) (t : Bool) :
    central p q c (fun _ => t) = 0 := by
  have h : ∃ j : Fin (m+1), WeightedMatching.binary (p j) (q j) t t = 0 :=
    ⟨0, by cases t <;> rfl⟩
  simp only [central]
  rw [Finset.prod_eq_zero (Finset.mem_univ h.choose) h.choose_spec, mul_zero]

lemma constants_ne : (fun _ : Ports m => false) ≠ (fun _ => true) := by
  intro h
  have h' := congrFun h (0,false)
  simp at h'

@[simp] lemma mountain_false (a b c : K) (p q : Fin (m+1) → K) :
    mountain a b c p q (fun _ => false) = a := by
  simp [mountain, constants_ne]

@[simp] lemma mountain_true (a b c : K) (p q : Fin (m+1) → K) :
    mountain a b c p q (fun _ => true) = b := by
  simp [mountain, Ne.symm constants_ne]

lemma opposite_not_constant (w : Ports m → Bool) (h : Opposite w) (t : Bool) :
    w ≠ (fun _ => t) := by
  rintro rfl
  have h' := h 0
  cases t <;> simp at h'

lemma mountain_of_opposite (a b c : K) (p q : Fin (m+1) → K)
    (w : Ports m → Bool) (h : Opposite w) :
    mountain a b c p q w = central p q c w := by
  simp [mountain, opposite_not_constant w h]

lemma mountain_ne_zero (a b c : K) (p q : Fin (m+1) → K)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : c * ∏ j, p j * q j ≠ 0)
    (w : Ports m → Bool) :
    mountain a b c p q w ≠ 0 ↔
      w = (fun _ => false) ∨ w = (fun _ => true) ∨ Opposite w := by
  by_cases h0 : w = (fun _ => false)
  · subst w; simp [ha]
  by_cases h1 : w = (fun _ => true)
  · subst w; simp [hb]
  simp [mountain, h0, h1, central_ne_zero p q c h]

def term (a b c : K) (p q : Fin (m+1) → K) (x : Fin 4 → Bool)
    (z : Edges m → Bool) : K :=
  mountain a b c p q (leftWord x z) * mountain a b c p q (rightWord x z)

def contract (a b c : K) (p q : Fin (m+1) → K) : Signature K 4 :=
  fun x => ∑ z : Edges m → Bool, term a b c p q x z

lemma boundary_eq (x : Fin 4 → Bool) (a b c d : Bool)
    (h0 : x 0 = a) (h1 : x 1 = b) (h2 : x 2 = c) (h3 : x 3 = d) :
    x = ![a,b,c,d] := by
  ext i; fin_cases i <;> simp_all

/-- Every nonzero summand is one of the two complementary endpoint assignments
or the unique central path assignment. This is proved from the actual wires. -/
lemma term_classify (hm : 2 ≤ m) (a b c : K) (p q : Fin (m+1) → K)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : c * ∏ j, p j * q j ≠ 0)
    (x : Fin 4 → Bool) (z : Edges m → Bool) (ht : term a b c p q x z ≠ 0) :
    (x = ![false,false,true,true] ∧ z = fun _ => false) ∨
    (x = ![true,true,false,false] ∧ z = fun _ => true) ∨
    (x 1 = !(x 0) ∧ x 3 = !(x 2) ∧ z = centerWord (x 2)) := by
  obtain ⟨hl,hr⟩ := mul_ne_zero_iff.mp ht
  rcases (mountain_ne_zero a b c p q ha hb h _).1 hl with hl | hl | hl
  · rcases (mountain_ne_zero a b c p q ha hb h _).1 hr with hr | hr | hr
    · obtain ⟨_,_,hz⟩ := (left_constant x z false).1 hl
      obtain ⟨_,_,hz'⟩ := (right_constant x z false).1 hr
      have := congrFun (hz.symm.trans hz') (⟨0,by omega⟩,false)
      simp at this
    · obtain ⟨h0,h1,hz⟩ := (left_constant x z false).1 hl
      obtain ⟨h2,h3,_⟩ := (right_constant x z true).1 hr
      exact Or.inl ⟨boundary_eq x _ _ _ _ h0 h1 h2 h3,hz⟩
    · exact False.elim (no_left_constant_right_opposite hm x z false hl hr)
  · rcases (mountain_ne_zero a b c p q ha hb h _).1 hr with hr | hr | hr
    · obtain ⟨h0,h1,hz⟩ := (left_constant x z true).1 hl
      obtain ⟨h2,h3,_⟩ := (right_constant x z false).1 hr
      exact Or.inr (Or.inl ⟨boundary_eq x _ _ _ _ h0 h1 h2 h3,hz⟩)
    · obtain ⟨_,_,hz⟩ := (left_constant x z true).1 hl
      obtain ⟨_,_,hz'⟩ := (right_constant x z true).1 hr
      have := congrFun (hz.symm.trans hz') (⟨0,by omega⟩,false)
      simp at this
    · exact False.elim (no_left_constant_right_opposite hm x z true hl hr)
  · rcases (mountain_ne_zero a b c p q ha hb h _).1 hr with hr | hr | hr
    · exact False.elim (no_left_opposite_right_constant (by omega) x z false hr hl)
    · exact False.elim (no_left_opposite_right_constant (by omega) x z true hr hl)
    · exact Or.inr (Or.inr (center_unique (by omega) x z hl hr))

lemma contract_central (hm : 2 ≤ m) (a b c : K) (p q : Fin (m+1) → K)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : c * ∏ j, p j * q j ≠ 0)
    (x : Fin 4 → Bool) (h01 : x 1 = !(x 0)) (h23 : x 3 = !(x 2)) :
    contract a b c p q x =
      central p q c (leftWord x (centerWord (x 2))) *
      central p q c (rightWord x (centerWord (x 2))) := by
  unfold contract
  rw [Finset.sum_eq_single (centerWord (x 2))]
  · obtain ⟨hl,hr⟩ := center_exists (m := m) x h01 h23
    simp [term, mountain_of_opposite a b c p q _ hl, mountain_of_opposite a b c p q _ hr]
  · intro z _ hz
    by_contra hn
    rcases term_classify hm a b c p q ha hb h x z hn with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨_,_,he⟩
    · simp at h01
    · simp at h01
    · exact hz he
  · simp

lemma contract_central_ne_zero (hm : 2 ≤ m) (a b c : K) (p q : Fin (m+1) → K)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : c * ∏ j, p j * q j ≠ 0)
    (x : Fin 4 → Bool) (h01 : x 1 = !(x 0)) (h23 : x 3 = !(x 2)) :
    contract a b c p q x ≠ 0 := by
  rw [contract_central hm a b c p q ha hb h x h01 h23]
  obtain ⟨hl,hr⟩ := center_exists (m := m) x h01 h23
  exact mul_ne_zero ((central_ne_zero p q c h _).2 hl) ((central_ne_zero p q c h _).2 hr)

lemma contract_endpoint (hm : 2 ≤ m) (a b c : K) (p q : Fin (m+1) → K)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : c * ∏ j, p j * q j ≠ 0) (t : Bool) :
    contract a b c p q ![t,t,!t,!t] = a*b := by
  unfold contract
  rw [Finset.sum_eq_single (fun _ => t)]
  · have hl : leftWord ![t,t,!t,!t] (fun _ : Edges m => t) = fun _ => t :=
      (left_constant _ _ t).2 ⟨rfl,rfl,rfl⟩
    have hr : rightWord ![t,t,!t,!t] (fun _ : Edges m => t) = fun _ => !t :=
      (right_constant _ _ (!t)).2 ⟨rfl,rfl,by simp⟩
    rw [term,hl,hr]
    cases t <;> simp [mul_comm]
  · intro z _ hz
    by_contra hn
    rcases term_classify hm a b c p q ha hb h _ z hn with ⟨hx,he⟩ | ⟨hx,he⟩ | ⟨hx,_,_⟩
    · have ht := congrFun hx 0
      simp at ht
      exact hz (by simpa [ht] using he)
    · have ht := congrFun hx 0
      simp at ht
      exact hz (by simpa [ht] using he)
    · cases t <;> simp at hx
  · simp

lemma contract_support (hm : 2 ≤ m) (a b c : K) (p q : Fin (m+1) → K)
    (ha : a ≠ 0) (hb : b ≠ 0) (h : c * ∏ j, p j * q j ≠ 0)
    (x : Fin 4 → Bool) :
    contract a b c p q x ≠ 0 ↔
      x = ![false,false,true,true] ∨ x = ![true,true,false,false] ∨
      (x 1 = !(x 0) ∧ x 3 = !(x 2)) := by
  constructor
  · intro hn
    have hex : ∃ z, term a b c p q x z ≠ 0 := by
      by_contra hn'
      push_neg at hn'
      exact hn (by simp [contract,hn'])
    obtain ⟨z,hz⟩ := hex
    rcases term_classify hm a b c p q ha hb h x z hz with ⟨hx,_⟩ | ⟨hx,_⟩ | ⟨h01,h23,_⟩
    · exact Or.inl hx
    · exact Or.inr (Or.inl hx)
    · exact Or.inr (Or.inr ⟨h01,h23⟩)
  · rintro (rfl | rfl | ⟨h01,h23⟩)
    · have he := contract_endpoint hm a b c p q ha hb h false
      simp only [Bool.not_false] at he
      rw [he]; exact mul_ne_zero ha hb
    · have he := contract_endpoint hm a b c p q ha hb h true
      simp only [Bool.not_true] at he
      rw [he]; exact mul_ne_zero ha hb
    · exact contract_central_ne_zero hm a b c p q ha hb h x h01 h23

end
end Paper2.TransversalCube
