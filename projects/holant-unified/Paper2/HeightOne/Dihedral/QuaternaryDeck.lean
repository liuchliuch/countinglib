import Paper2.HeightOne.Dihedral.Quaternary
import Paper2.HeightOne.Parity

/-! The RN coefficient hypotheses on an actual four-port table, in every
ordered xor sector and at every base word. Offset changes are analytic index
changes only. The finite Boolean geometry is checked in the kernel. -/
namespace Paper2.HeightOne.Dihedral
open Tractable PhasePencil
noncomputable section

abbrev Word4 := Fin 4 → Bool

def flipAll (a : Word4) : Word4 := fun k => !(a k)
def flipPair (i j : Fin 4) (a : Word4) : Word4 :=
  fun k => if k = i ∨ k = j then !(a k) else a k

def centralWord (i : Fin 3) (a : Word4) : Word4 := flipPair 0 i.succ a

def otherFirst (i : Fin 3) : Fin 4 := ![2, 1, 1] i
def otherSecond (i : Fin 3) : Fin 4 := ![3, 3, 2] i

def FullQuaternaryDeck (N : ℕ) (f : Signature AlgebraicComplex 4) : Prop :=
  ∀ i j : Fin 4, i ≠ j → ∀ a : Word4,
    Relation N (f a) (f (flipPair i j a))
      (f (flipAll (flipPair i j a))) (f (flipAll a))

@[simp] lemma flipAll_flipAll (a : Word4) : flipAll (flipAll a) = a := by
  funext k
  simp [flipAll]

lemma other_distinct (i : Fin 3) : otherFirst i ≠ otherSecond i := by
  fin_cases i <;> decide

lemma flip_other_pair (i : Fin 3) (a : Word4) :
    flipPair (otherFirst i) (otherSecond i) a = flipAll (centralWord i a) := by
  fin_cases i <;> funext k <;> fin_cases k <;>
    simp [otherFirst, otherSecond, flipPair, centralWord, flipAll]

lemma flip_central_pair (i j : Fin 3) (hij : i ≠ j) (a : Word4) :
    flipPair i.succ j.succ (centralWord i a) = centralWord j a := by
  fin_cases i <;> fin_cases j <;> try exact False.elim (hij rfl)
  all_goals funext k
  all_goals fin_cases k <;> simp [flipPair, centralWord]

/-- All eight words in the base word's parity class, without quotienting by
complement or dropping the distinction between the two orientations. -/
lemma parity_word_cover (a x : Word4) (h : parity x = parity a) :
    x = a ∨ x = flipAll a ∨
      (∃ i : Fin 3, x = centralWord i a) ∨
      (∃ i : Fin 3, x = flipAll (centralWord i a)) := by
  have H : ∀ a x : Word4, parity x = parity a →
      x = a ∨ x = flipAll a ∨
        (∃ i : Fin 3, x = centralWord i a) ∨
        (∃ i : Fin 3, x = flipAll (centralWord i a)) := by decide
  exact H a x h

theorem fullDeck_relations {N : ℕ} {f : Signature AlgebraicComplex 4}
    (h : FullQuaternaryDeck N f) (a : Word4) :
    QuaternaryRelations N (f a) (f (flipAll a))
      (fun i => f (centralWord i a)) (fun i => f (flipAll (centralWord i a))) := by
  constructor
  · intro i
    constructor
    · exact h 0 i.succ (by intro he; have := congrArg Fin.val he; simp at this) a
    · have hh := h (otherFirst i) (otherSecond i) (other_distinct i) a
      simpa only [flip_other_pair, flipAll_flipAll] using hh
  · intro i j hij
    have hh := h i.succ j.succ (fun he => hij (Fin.succ_inj.mp he)) (centralWord i a)
    simpa only [flip_central_pair i j hij] using hh

/-- Any nonzero single-parity table with the complete odd-dihedral RN deck has
one or two complete complementary support pairs. The leading nonzero entry
can be any original word, so this covers even and odd Walsh parity together. -/
theorem fullDeck_support_pairs {N : ℕ} (hodd : Odd N)
    {f : Signature AlgebraicComplex 4} (hpar : HasParity f)
    (hdeck : FullQuaternaryDeck N f) (a : Word4) (ha : f a ≠ 0) :
    f (flipAll a) ≠ 0 ∧ (∃ r, Root N r ∧ f (flipAll a) = r * f a) ∧
      ((∀ x, f x ≠ 0 → x = a ∨ x = flipAll a) ∨
       ∃ i : Fin 3, ∃ α β : AlgebraicComplex, Root N α ∧ Root N β ∧
         f (centralWord i a) = -α * f a ∧
         f (flipAll (centralWord i a)) = -β * f a ∧
         f (flipAll a) = (α * β) * f a ∧
         ∀ x, f x ≠ 0 → x = a ∨ x = flipAll a ∨
           x = centralWord i a ∨ x = flipAll (centralWord i a)) := by
  classical
  obtain ⟨ht, hr, hrow, huni⟩ := quaternary_live_endpoint hodd ha (fullDeck_relations hdeck a)
  refine ⟨ht, hr, ?_⟩
  by_cases hlive : ∃ i : Fin 3, f (centralWord i a) ≠ 0
  · right
    obtain ⟨i, hi⟩ := hlive
    obtain hz | ⟨α, β, hα, hβ, hxi, hyi, hti⟩ := hrow i
    · exact False.elim (hi hz.1)
    refine ⟨i, α, β, hα, hβ, hxi, hyi, hti, ?_⟩
    intro x hx
    rcases parity_word_cover a x (hpar x a hx ha) with he | he | ⟨j,he⟩ | ⟨j,he⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · have hj : f (centralWord j a) ≠ 0 := by simpa [he] using hx
      have heji : j = i := huni j i hj hi
      exact Or.inr (Or.inr (Or.inl (by simpa [heji] using he)))
    · have hj : f (centralWord j a) ≠ 0 := by
        intro hj0
        rcases hrow j with hz | ⟨r,s,hr,hs,he,_,_⟩
        · exact hx (by simpa [he] using hz.2)
        · exact mul_ne_zero (neg_ne_zero.mpr (root_ne_zero hodd.pos hr)) ha (he.symm.trans hj0)
      have heji : j = i := huni j i hj hi
      exact Or.inr (Or.inr (Or.inr (by simpa [heji] using he)))
  · left
    intro x hx
    rcases parity_word_cover a x (hpar x a hx ha) with he | he | ⟨i,he⟩ | ⟨i,he⟩
    · exact Or.inl he
    · exact Or.inr he
    · exact False.elim (hlive ⟨i, by simpa [he] using hx⟩)
    · rcases hrow i with hz | ⟨r,s,hr,hs,hri,_,_⟩
      · exact False.elim (hx (by simpa [he] using hz.2))
      · exact False.elim (hlive ⟨i, hri.symm ▸ mul_ne_zero
          (neg_ne_zero.mpr (root_ne_zero hodd.pos hr)) ha⟩)

end
end Paper2.HeightOne.Dihedral
