import ComplexCSP.Algebra.GramObstruction
import Mathlib.LinearAlgebra.Matrix.PosDef

/-! # Explicit positive powers of connected nonnegative matrices

Repeated squaring expands each positive row support strictly until it fills the
finite connected component. The same strict principal minor survives every
squaring by the finite Cauchy–Schwarz identity. No rank or hardness oracle occurs.
-/
noncomputable section
open Classical
set_option backward.isDefEq.respectTransparency false

namespace ComplexCSP.PositiveGramPower
open scoped BigOperators
variable {I : Type} [Fintype I]

def squarePower (A : Matrix I I ℝ) : ℕ → Matrix I I ℝ
  | 0 => A
  | n+1 => squarePower A n * squarePower A n

theorem squarePower_eq [DecidableEq I] (A : Matrix I I ℝ) (n : ℕ) :
    squarePower A n=A^(2^n) := by
  induction n with
  | zero => simp [squarePower]
  | succ n ih =>
    rw [squarePower,ih,←pow_add]
    congr 1
    simp [Nat.pow_succ,Nat.mul_two]

def Connected (A : Matrix I I ℝ) : Prop :=
  ∀ i j,Relation.ReflTransGen (fun x y => 0<A x y) i j

theorem square_nonneg (A : Matrix I I ℝ) (hA : ∀ i j,0≤A i j) :
    ∀ i j,0≤(A*A) i j := by
  intro i j
  exact Finset.sum_nonneg (fun k _ => mul_nonneg (hA i k) (hA k j))

theorem square_positive_term (A : Matrix I I ℝ) (hA : ∀ i j,0≤A i j)
    (i j k : I) (hik : 0<A i k) (hkj : 0<A k j) : 0<(A*A) i j := by
  exact (mul_pos hik hkj).trans_le
    (Finset.single_le_sum (fun l _ => mul_nonneg (hA i l) (hA l j)) (Finset.mem_univ k))

theorem squarePower_nonneg (A : Matrix I I ℝ) (hA : ∀ i j,0≤A i j) :
    ∀ n i j,0≤squarePower A n i j := by
  intro n
  induction n with
  | zero => exact hA
  | succ n ih => exact square_nonneg _ ih

theorem squarePower_diagonal (A : Matrix I I ℝ) (hA : ∀ i j,0≤A i j)
    (hd : ∀ i,0<A i i) : ∀ n i,0<squarePower A n i i := by
  intro n
  induction n with
  | zero => exact hd
  | succ n ih => exact fun i => square_positive_term _ (squarePower_nonneg A hA n) i i i (ih i) (ih i)

theorem positive_mono_step (A : Matrix I I ℝ) (hA : ∀ i j,0≤A i j)
    (hd : ∀ i,0<A i i) (n : ℕ) (i j : I) (hij : 0<squarePower A n i j) :
    0<squarePower A (n+1) i j :=
  square_positive_term _ (squarePower_nonneg A hA n) i j j hij (squarePower_diagonal A hA hd n j)

theorem original_positive (A : Matrix I I ℝ) (hA : ∀ i j,0≤A i j)
    (hd : ∀ i,0<A i i) (n : ℕ) (i j : I) (hij : 0<A i j) :
    0<squarePower A n i j := by
  induction n with
  | zero => exact hij
  | succ n ih => exact positive_mono_step A hA hd n i j ih

def rowSupport (A : Matrix I I ℝ) (n : ℕ) (i : I) : Finset I :=
  Finset.univ.filter (fun j => 0<squarePower A n i j)

theorem support_mono (A : Matrix I I ℝ) (hA : ∀ i j,0≤A i j)
    (hd : ∀ i,0<A i i) (i : I) : Monotone (fun n => rowSupport A n i) := by
  apply monotone_nat_of_le_succ
  intro n j hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    positive_mono_step A hA hd n i j (Finset.mem_filter.mp hj).2⟩

private theorem exists_boundary (A : Matrix I I ℝ) (hc : Connected A)
    (S : Finset I) (i : I) (hi : i∈S) (hS : S≠Finset.univ) :
    ∃ x y,x∈S ∧ y∉S ∧ 0<A x y := by
  by_contra h
  push_neg at h
  have hclosed : ∀ x y,x∈S → 0<A x y → y∈S := by
    intro x y hx hxy
    by_contra hy
    exact (not_lt_of_ge (h x y hx hy)) hxy
  apply hS
  apply Finset.eq_univ_of_forall
  intro j
  have hj := hc i j
  induction hj with
  | refl => exact hi
  | tail hab hbc ih => exact hclosed _ _ ih hbc

theorem support_grows (A : Matrix I I ℝ) (hA : ∀ i j,0≤A i j)
    (hd : ∀ i,0<A i i) (hc : Connected A) (n : ℕ) (i : I)
    (hS : rowSupport A n i≠Finset.univ) :
    (rowSupport A n i).card < (rowSupport A (n+1) i).card := by
  have hii : i∈rowSupport A n i := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,squarePower_diagonal A hA hd n i⟩
  obtain ⟨x,y,hx,hy,hxy⟩ := exists_boundary A hc _ i hii hS
  have hnext : y∈rowSupport A (n+1) i := Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    square_positive_term _ (squarePower_nonneg A hA n) i y x
      (Finset.mem_filter.mp hx).2 (original_positive A hA hd n x y hxy)⟩
  apply Finset.card_lt_card
  refine Finset.ssubset_iff_subset_ne.mpr ⟨support_mono A hA hd i (Nat.le_succ n),?_⟩
  intro he
  exact hy (he.symm ▸ hnext)

/-- The explicit power A^(2^|I|) is entrywise positive on a connected support
with positive diagonal; the exponent is independent of any search oracle. -/
theorem squarePower_positive (A : Matrix I I ℝ) (hA : ∀ i j,0≤A i j)
    (hd : ∀ i,0<A i i) (hc : Connected A) :
    ∀ i j,0<squarePower A (Fintype.card I) i j := by
  intro i j
  have hfull : rowSupport A (Fintype.card I) i=Finset.univ := by
    by_contra hlast
    have hproper (n : ℕ) (hn : n≤Fintype.card I) : rowSupport A n i≠Finset.univ := by
      intro he
      apply hlast
      apply Finset.Subset.antisymm (Finset.subset_univ _)
      rw [←he]
      exact support_mono A hA hd i hn
    have hcard (n : ℕ) (hn : n≤Fintype.card I) : n+1≤(rowSupport A n i).card := by
      induction n with
      | zero =>
        have hi : i∈rowSupport A 0 i := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hd i⟩
        exact Finset.card_pos.mpr ⟨i,hi⟩
      | succ n ih =>
        have hn' : n≤Fintype.card I := by omega
        have hb := ih hn'
        have hs := support_grows A hA hd hc n i (hproper n hn')
        omega
    have hlo := hcard (Fintype.card I) le_rfl
    have hhi := Finset.card_le_card (Finset.subset_univ (rowSupport A (Fintype.card I) i))
    simp only [Finset.card_univ] at hhi
    omega
  have hj : j∈rowSupport A (Fintype.card I) i := by rw [hfull]; exact Finset.mem_univ j
  exact (Finset.mem_filter.mp hj).2

def StrictMinor (A : Matrix I I ℝ) (i j : I) : Prop :=
  0<A i i ∧ 0<A i j ∧ 0<A j j ∧ A i j*A j i < A i i*A j j

theorem square_eq_gram (A : Matrix I I ℝ) (hs : ∀ i j,A i j=A j i) (i j : I) :
    (A*A) i j=GramObstruction.gram A i j := by
  rw [Matrix.mul_apply,GramObstruction.gram]
  apply Finset.sum_congr rfl
  intro z _
  rw [hs z j]

theorem square_symm (A : Matrix I I ℝ) (hs : ∀ i j,A i j=A j i) :
    ∀ i j,(A*A) i j=(A*A) j i := by
  intro i j
  rw [square_eq_gram A hs,square_eq_gram A hs,GramObstruction.gram_symm]

/-- The very same principal pair stays strict after squaring. This is stronger
than the required rank-preservation conclusion and uses only finite sums. -/
theorem square_strict_minor (A : Matrix I I ℝ) (hA : ∀ i j,0≤A i j)
    (hs : ∀ i j,A i j=A j i) (i j : I) (hm : StrictMinor A i j) :
    StrictMinor (A*A) i j := by
  obtain ⟨hii,hij,hjj,hdet⟩ := hm
  refine ⟨square_positive_term A hA i i i hii hii,
    square_positive_term A hA i j i hii hij,
    square_positive_term A hA j j j hjj hjj,?_⟩
  rw [square_symm A hs j i,←pow_two,square_eq_gram A hs i j,
    square_eq_gram A hs i i,square_eq_gram A hs j j]
  exact GramObstruction.strict_cauchy_of_minor (A i) (A j) i j (ne_of_gt hdet)

theorem squarePower_symm (A : Matrix I I ℝ) (hs : ∀ i j,A i j=A j i) :
    ∀ n i j,squarePower A n i j=squarePower A n j i := by
  intro n
  induction n with
  | zero => exact hs
  | succ n ih => exact square_symm _ ih

theorem squarePower_strict_minor (A : Matrix I I ℝ) (hA : ∀ i j,0≤A i j)
    (hs : ∀ i j,A i j=A j i) (i j : I) (hm : StrictMinor A i j) :
    ∀ n,StrictMinor (squarePower A n) i j := by
  intro n
  induction n with
  | zero => exact hm
  | succ n ih =>
      exact square_strict_minor _ (squarePower_nonneg A hA n)
        (squarePower_symm A hs n) i j ih

/-- An explicit fixed strictly positive matrix power retaining the actual
principal obstruction pair. No spectral decomposition, eigenvalue bound,
rank assumption, or positive-power existence oracle is used. -/
theorem positive_power_and_minor [DecidableEq I]
    (A : Matrix I I ℝ) (hA : ∀ i j,0≤A i j) (hd : ∀ i,0<A i i)
    (hc : Connected A) (hs : ∀ i j,A i j=A j i) (i j : I) (hm : StrictMinor A i j) :
    (∀ x y,0<(A^(2^Fintype.card I)) x y) ∧ StrictMinor (A^(2^Fintype.card I)) i j := by
  rw [←squarePower_eq]
  exact ⟨squarePower_positive A hA hd hc,squarePower_strict_minor A hA hs i j hm _⟩

omit [Fintype I] in
/-- Positive Gram entries force positive diagonal entries at both endpoints.
This supplies the diagonal premise after restricting to a nontrivial component. -/
theorem gram_diagonal_of_positive {C : Type} [Fintype C] (B : I → C → ℝ)
    (hB : ∀ i z,0≤B i z) (i j : I) (hij : 0<GramObstruction.gram B i j) :
    0<GramObstruction.gram B i i ∧ 0<GramObstruction.gram B j j := by
  obtain ⟨z,hz,hpos⟩ := (Finset.sum_pos_iff_of_nonneg (fun z _ => mul_nonneg (hB i z) (hB j z))).mp hij
  have hi : 0<B i z := pos_of_mul_pos_left hpos (hB j z)
  have hj : 0<B j z := pos_of_mul_pos_right hpos (hB i z)
  exact ⟨GramObstruction.gram_pos_of_common B hB i i z hi hi,
    GramObstruction.gram_pos_of_common B hB j j z hj hj⟩

omit [Fintype I] in
/-- Every vertex reached from a positive diagonal in a nonnegative Gram support
has a positive diagonal, including paths of length zero. -/
theorem gram_diagonal_on_component {C : Type} [Fintype C] (B : I → C → ℝ)
    (hB : ∀ i z,0≤B i z) {i j : I} (hi : 0<GramObstruction.gram B i i)
    (hij : Relation.ReflTransGen (fun x y => 0<GramObstruction.gram B x y) i j) :
    0<GramObstruction.gram B j j := by
  induction hij with
  | refl => exact hi
  | tail hab hbc ih => exact (gram_diagonal_of_positive B hB _ _ hbc).2

end ComplexCSP.PositiveGramPower
