import Paper2.RelativeEO.QuaternarySupport
import Paper2.RelativeEO.PairTable

/-! From the complete six-support analysis to actual ordered tensor forms.
Compressed tables are used only as algebraic coordinates and class witnesses. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.RelativeEO
open Paper2.Tractable

noncomputable def sixSupport (f : Signature AlgebraicComplex 4) (j : Fin 6) : Bool :=
  decide (f (sixWord j) ≠ 0)

@[simp] theorem sixSupport_eq_true (f : Signature AlgebraicComplex 4) (j : Fin 6) :
    sixSupport f j = true ↔ f (sixWord j) ≠ 0 := by
  classical
  simp [sixSupport]

theorem central_of_nonzero (f : Signature AlgebraicComplex 4)
    (he : Signature.CentralSupport f) (x : Fin 4 → Bool) (hx : f x ≠ 0) : weight x = 2 := by
  by_contra hn
  apply hx
  apply he
  change 2 * weight x ≠ 4
  omega

theorem fixed_of_sixFixed (f : Signature AlgebraicComplex 4)
    (he : Signature.CentralSupport f) (h : SixFixed (sixSupport f)) :
    ∃ i : Fin 4, ∃ b : Bool, ∀ x, f x ≠ 0 → x i = b := by
  obtain ⟨i,b,h⟩ := h
  refine ⟨i,b,?_⟩
  intro x hx
  obtain ⟨j,rfl⟩ := centralWord_exists x (central_of_nonzero f he x hx)
  exact h j (by simpa using hx)

theorem complementary_of_sixComplementary (f : Signature AlgebraicComplex 4)
    (he : Signature.CentralSupport f) (h : SixComplementary (sixSupport f)) :
    ∃ (s : Fin 4 → Bool) (p q : AlgebraicComplex), weight s = 2 ∧ p ≠ 0 ∧ q ≠ 0 ∧
      f = complementaryTable s p q := by
  classical
  obtain ⟨j,h⟩ := h
  let s := sixWord j
  have hs : s ≠ (fun i => !(s i)) := by
    intro heq
    have heq' := congrFun heq 0
    exact Bool.not_ne_self (s 0) heq'.symm
  have hp : f s ≠ 0 := (sixSupport_eq_true f j).mp ((h j).mpr (Or.inl rfl))
  have hq : f (fun i => !(s i)) ≠ 0 := by
    rw [← sixWord_dual]
    exact (sixSupport_eq_true f (sixDual j)).mp ((h (sixDual j)).mpr (Or.inr (sixWord_dual j)))
  refine ⟨s,f s,f (fun i => !(s i)),sixWord_weight j,hp,hq,?_⟩
  funext x
  by_cases hx : x = s
  · subst x
    simp [complementaryTable,hs]
  · by_cases hx' : x = (fun i => !(s i))
    · subst x
      simp [complementaryTable,Ne.symm hs]
    · have hz : f x = 0 := by
        by_contra hn
        obtain ⟨k,hk⟩ := centralWord_exists x (central_of_nonzero f he x hn)
        have hkn : sixSupport f k = true := by simpa [hk] using hn
        rcases (h k).mp hkn with hh | hh
        · exact hx (hk.symm.trans hh)
        · exact hx' (hk.symm.trans hh)
      simp [complementaryTable,hx,hx',hz]

/-- Each of the three matching supports is brought to consecutive ordered
pairs by one fixed port swap. This is an actual boundary permutation. -/
def matchingPerm (j : Fin 3) : Equiv.Perm (Fin 4) :=
  Equiv.swap 1 ⟨j.val+1,by omega⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem matchingPerm_support : ∀ (j : Fin 3) (x : Fin 4 → Bool),
    (∃ k : Fin 6, sixWord k = (fun i => x (matchingPerm j i)) ∧
      k.val ≠ j.val ∧ k.val ≠ 5-j.val) ↔ x 1 = !(x 0) ∧ x 3 = !(x 2) := by
  unfold matchingPerm
  decide +kernel

/-- Transport a pairing backwards through precisely the boundary permutation. -/
def pairingThrough (e : Equiv.Perm (Fin 4)) : OrientedPerfectPairing 4 :=
  ⟨2,canonicalPairing.ports.trans e.symm⟩

@[simp] theorem pairingThrough_restrict (e : Equiv.Perm (Fin 4))
    (f : Signature AlgebraicComplex 4) :
    (pairingThrough e).restrict f = canonicalPairing.restrict (Tensor.reindex e f) := rfl

theorem canonicalPairing_word_eta (x : Fin 4 → Bool)
    (hx : x 1 = !(x 0) ∧ x 3 = !(x 2)) :
    canonicalPairing.word (binWord (x 0) (x 2)) = x := by
  funext i
  fin_cases i
  · rfl
  · exact hx.1.symm
  · rfl
  · exact hx.2.symm

theorem canonicalPairing_word_opposite (z : Fin 2 → Bool) :
    (canonicalPairing.word z) 1 = !((canonicalPairing.word z) 0) ∧
    (canonicalPairing.word z) 3 = !((canonicalPairing.word z) 2) := by
  constructor <;> rfl

/-- A matching support gives a literal pair-table normal form and full support
of its compressed binary coordinates. -/
theorem pairForm_of_sixMatching (f : Signature AlgebraicComplex 4)
    (he : Signature.CentralSupport f) (h : SixMatching (sixSupport f)) :
    ∃ e : Equiv.Perm (Fin 4), ∃ g : Signature AlgebraicComplex 2,
      Tensor.reindex e f = pairTable g ∧ (∀ z, g z ≠ 0) ∧
        g = (pairingThrough e).restrict f := by
  classical
  obtain ⟨j,h⟩ := h
  let e := matchingPerm j
  let q := Tensor.reindex e f
  let g := canonicalPairing.restrict q
  have hs (x : Fin 4 → Bool) : q x ≠ 0 ↔ x 1 = !(x 0) ∧ x 3 = !(x 2) := by
    rw [← matchingPerm_support j x]
    constructor
    · intro hx
      obtain ⟨k,hk⟩ := centralWord_exists (fun i => x (e i)) (central_of_nonzero f he _ hx)
      exact ⟨k,hk,(h k).mp (by simpa [hk,sixSupport,q,Tensor.reindex,e] using hx)⟩
    · rintro ⟨k,hk,hk'⟩
      have hn := (sixSupport_eq_true f k).mp ((h k).mpr hk')
      simpa [hk,q,Tensor.reindex,e] using hn
  refine ⟨e,g,?_,?_,rfl⟩
  · funext x
    change q x = pairTable g x
    by_cases hx : x 1 = !(x 0) ∧ x 3 = !(x 2)
    · simp only [pairTable,if_pos hx]
      exact congrArg q (canonicalPairing_word_eta x hx).symm
    · simp only [pairTable,if_neg hx]
      exact not_not.mp (mt (hs x).mp hx)
  · intro z
    exact (hs (canonicalPairing.word z)).mpr (canonicalPairing_word_opposite z)

/-- All quaternary EOTract possibilities are genuine fixed-port, complementary,
or pair-supported forms. One source-wide A/P choice supplies the compressed
class in the third alternative. -/
theorem eoTract_quaternary_forms (F : SignatureFamily AlgebraicComplex) (h : EOTract F)
    (f : Signature AlgebraicComplex 4)
    (hmem : (⟨4,f⟩ : AnySignature AlgebraicComplex) ∈ F) :
    (∃ i : Fin 4, ∃ b : Bool, ∀ x, f x ≠ 0 → x i = b) ∨
    (∃ (s : Fin 4 → Bool) (p q : AlgebraicComplex), weight s = 2 ∧ p ≠ 0 ∧ q ≠ 0 ∧
      f = complementaryTable s p q) ∨
    (∃ e : Equiv.Perm (Fin 4), ∃ g : Signature AlgebraicComplex 2,
      Tensor.reindex e f = pairTable g ∧ (∀ z, g z ≠ 0) ∧ (Affine g ∨ Product g)) := by
  obtain ⟨positive,htr⟩ := eoTract_sixTriple F h f hmem
  have he := (h.2.1 ⟨4,f⟩ hmem).2
  rcases six_support_classification (sixSupport f) positive htr with hfix | hcomp | hpair
  · exact Or.inl (fixed_of_sixFixed f he hfix)
  · exact Or.inr (Or.inl (complementary_of_sixComplementary f he hcomp))
  · obtain ⟨e,g,hg,hn,hgf⟩ := pairForm_of_sixMatching f he hpair
    obtain ⟨_,C,_,hclass⟩ := h.2.2
    have hc := hclass ⟨4,f⟩ hmem (pairingThrough e)
    rw [← hgf] at hc
    refine Or.inr (Or.inr ⟨e,g,hg,hn,?_⟩)
    cases C with
    | affine => exact Or.inl hc
    | product => exact Or.inr hc

end Paper2.RelativeEO
