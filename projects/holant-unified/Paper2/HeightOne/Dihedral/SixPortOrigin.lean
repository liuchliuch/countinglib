import Paper2.HeightOne.Dihedral.SixPortPencils
import Paper2.HeightOne.Cyclic.ActualDeck

/-! A nonzero origin turns the signed matching cosets of the dihedral cards
into the equality matching supports needed by the proved logical-cube
reconstruction. The support union bound is used literally, including zero
pencil members. -/
namespace Paper2.HeightOne.Dihedral
noncomputable section
open Cyclic
variable {K : Type*} [Field K]
local instance {ι : Type} : DecidableEq ι := Classical.decEq ι

def cosetCode {n : ℕ} (P : Pairing n) (a : Fin n → Bool) : Finset (Fin n → Bool) := by
  classical
  exact (equalityCode P).image (xorWord a)

lemma xorWord_injective {ι : Type} (a : ι → Bool) : Function.Injective (xorWord a) := by
  intro x y h
  funext i
  have hi := congrFun h i
  simp only [xorWord] at hi
  cases ha : a i <;> simpa only [ha, Bool.false_xor, Bool.true_xor, Bool.not_inj_iff] using hi

lemma cosetCode_card {n : ℕ} (P : Pairing n) (a : Fin n → Bool) :
    (cosetCode P a).card = 2 ^ (n / 2) := by
  classical
  rw [cosetCode, Finset.card_image_of_injective _ (xorWord_injective a), equalityCode_card]

lemma cosetCode_matchingWords {n : ℕ} (P : Pairing n) (d : Fin P.count → Bool) :
    cosetCode P (Matching.word P d (fun _ => false)) =
      Finset.univ.image (Matching.word P d) := by
  classical
  rw [cosetCode,equalityCode_eq_image,Finset.image_image]
  congr 1
  funext z k
  obtain ⟨⟨j,b⟩,rfl⟩ := P.ports.surjective k
  cases b <;> simp [xorWord,Matching.word_first,Matching.word_second,Bool.xor_comm]

lemma cosetCode_origin {n : ℕ} (P : Pairing n) (a : Fin n → Bool)
    (h0 : (fun _ => false) ∈ cosetCode P a) : cosetCode P a = equalityCode P := by
  classical
  obtain ⟨b, hb, he⟩ := Finset.mem_image.mp h0
  have ha : a ∈ equalityCode P := by
    have hab : a = b := by
      funext i
      have hi := congrFun he i
      cases ha : a i <;> cases hh : b i <;> simp_all [xorWord]
    simpa only [hab] using hb
  ext x
  constructor
  · rintro hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hx
    exact equalityCode_xorClosed P a ha y hy
  · intro hx
    refine Finset.mem_image.mpr ⟨xorWord a x, equalityCode_xorClosed P a ha x hx, ?_⟩
    funext i
    simp only [xorWord]
    cases a i <;> cases x i <;> rfl

/-- The literal affine matching support of a product of nonzero complementary
binary factors, with the external port order retained. -/
def CosetMatchingSupport {ι : Type} [Fintype ι] (f : Tensor K ι) : Prop :=
  ∃ P : Pairing (Fintype.card ι), ∃ a,
    support (Tensor.reindex (Fintype.equivFin ι) f) = cosetCode P a

lemma CosetMatchingSupport.card {ι : Type} [Fintype ι] {f : Tensor K ι}
    (h : CosetMatchingSupport f) : (support f).card = 2 ^ (Fintype.card ι / 2) := by
  classical
  obtain ⟨P,a,h⟩ := h
  have he : support (Tensor.reindex (Fintype.equivFin ι) f) =
      (support f).image (fun x => fun j => x ((Fintype.equivFin ι).symm j)) := by
    ext y
    simp only [mem_support,Tensor.reindex_apply,Finset.mem_image]
    constructor
    · intro hy
      refine ⟨fun i => y ((Fintype.equivFin ι) i), ?_, ?_⟩
      · simpa only [Equiv.apply_symm_apply] using hy
      · simp only [Equiv.apply_symm_apply]
    · rintro ⟨x,hx,rfl⟩
      simpa only [Equiv.symm_apply_apply] using hx
  have hinj : Function.Injective (fun x : ι → Bool => fun j => x ((Fintype.equivFin ι).symm j)) := by
    intro x y hxy
    funext i
    simpa only [Equiv.symm_apply_apply] using congrFun hxy ((Fintype.equivFin ι) i)
  have hh := congrArg Finset.card he
  rw [h,cosetCode_card,Finset.card_image_of_injective _ hinj] at hh
  exact hh.symm

lemma CosetMatchingSupport.equality_of_origin {ι : Type} [Fintype ι] {f : Tensor K ι}
    (h : CosetMatchingSupport f) (h0 : f (fun _ => false) ≠ 0) : EqualityMatchingSupport f := by
  obtain ⟨P,a,h⟩ := h
  refine ⟨P, h.trans (cosetCode_origin P a ?_)⟩
  rw [← h,mem_support]
  exact h0

lemma pencil_support_eq_joint {X : Type*} [Fintype X] (A B : X → K) (s : K)
    (c : ℕ) (hU : (jointSupport A B).card ≤ c)
    (hcard : (pencilSupport A B s).card = c) :
    pencilSupport A B s = jointSupport A B := by
  classical
  exact Finset.eq_of_subset_of_card_le (pencilSupport_subset A B s) (by omega)

/-- A nonzero matching card has the full common support. In particular the
origin cannot cancel in just one nonzero member of a four-point pencil. -/
theorem matching_pencil_of_union_bound {ι : Type} [Fintype ι]
    (A B : (ι → Bool) → K) (s : K)
    (h0 : A (fun _ => false) ≠ 0 ∨ B (fun _ => false) ≠ 0)
    (hU : (jointSupport A B).card ≤ 2 ^ (Fintype.card ι / 2))
    (hcoset : CosetMatchingSupport (fun x => A x - s * B x)) :
    EqualityMatchingSupport (fun x => A x - s * B x) := by
  classical
  have hcard : (pencilSupport A B s).card = 2 ^ (Fintype.card ι / 2) := by
    simpa only [pencilSupport, support] using hcoset.card
  have he := pencil_support_eq_joint A B s _ hU hcard
  apply hcoset.equality_of_origin
  have hm : (fun _ => false) ∈ jointSupport A B := (mem_jointSupport _ _ _).mpr h0
  rw [← he,mem_pencilSupport] at hm
  exact hm

end
end Paper2.HeightOne.Dihedral
