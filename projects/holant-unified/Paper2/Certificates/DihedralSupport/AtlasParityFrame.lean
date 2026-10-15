import Paper2.Certificates.DihedralSupport.AtlasVectors
import Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion

/-! The literal parity-word frame of the Appendix A.1 atlas. Each block is
oriented by its first bit; its two words are exact bitwise complements. -/
namespace Paper2.Certificates.DihedralSupport.AtlasParityFrame
open Paper2.HeightOne Paper2.HeightOne.Cyclic
open Paper2.HeightOne.Dihedral Paper2.HeightOne.Dihedral.SixPortSupport
open AtlasCounts AtlasVectors
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def coordinates (x : Word4) : Coordinate :=
  (⟨2 * (x 0 ^^ x 1).toNat + (x 0 ^^ x 2).toNat,by
    cases h1 : (x 0 ^^ x 1) <;> cases h2 : (x 0 ^^ x 2) <;> decide⟩,x 0)

def word (epsilon : Bool) (c : Coordinate) : Word4 :=
  ![c.2, c.2 ^^ decide (2 ≤ c.1.val), c.2 ^^ decide (c.1.val % 2 = 1),
    c.2 ^^ decide (2 ≤ c.1.val) ^^ decide (c.1.val % 2 = 1) ^^ epsilon]

theorem word_parity : ∀ epsilon c, parity (word epsilon c) = epsilon.toNat := by
  decide +kernel

theorem coordinates_word : ∀ epsilon c, coordinates (word epsilon c) = c := by
  decide +kernel

theorem word_coordinates : ∀ epsilon x,
    parity x = epsilon.toNat → word epsilon (coordinates x) = x := by
  decide +kernel

theorem coordinates_complement : ∀ x,
    coordinates (complement x) = ((coordinates x).1,!(coordinates x).2) := by
  decide +kernel

theorem word_injective (epsilon : Bool) : Function.Injective (word epsilon) := by
  intro c d h
  have hc := congrArg coordinates h
  simpa only [coordinates_word] using hc

variable {K : Type} [Field K]

def extendVector (epsilon : Bool) (v : Coordinate → K) : Signature K 4 :=
  fun x => if parity x = epsilon.toNat then v (coordinates x) else 0

def table (omega : K) (epsilon : Bool) (l : PointLabel) : Signature K 4 :=
  extendVector epsilon (vector omega l)

theorem extendVector_word (epsilon : Bool) (v : Coordinate → K) (c : Coordinate) :
    extendVector epsilon v (word epsilon c) = v c := by
  simp [extendVector,word_parity,coordinates_word]

theorem table_word (omega : K) (epsilon : Bool) (l : PointLabel) (c : Coordinate) :
    table omega epsilon l (word epsilon c) = vector omega l c := by
  exact extendVector_word epsilon _ c

theorem table_complement_cube (omega : K) (homega : omega ^ 3 = 1)
    (epsilon : Bool) (l : PointLabel) (x : Word4) :
    table omega epsilon l (complement x) ^ 3 = table omega epsilon l x ^ 3 := by
  by_cases hp : parity x = epsilon.toNat
  · simp only [table,extendVector,parity_complement,hp,ite_true,coordinates_complement]
    rcases hc : coordinates x with ⟨p,b⟩
    cases b
    · simpa [hc] using AtlasVectors.complement_cube omega homega l p
    · simpa [hc] using (AtlasVectors.complement_cube omega homega l p).symm
  · simp [table,extendVector,parity_complement,hp]

theorem table_support_image (omega : K) (epsilon : Bool) (l : PointLabel)
    (S : Finset Coordinate) (hS : ∀ c, vector omega l c ≠ 0 ↔ c ∈ S) :
    Cyclic.support (table omega epsilon l) = S.image (word epsilon) := by
  classical
  ext x
  simp only [Cyclic.support,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
  constructor
  · intro hx
    have hp : parity x = epsilon.toNat := by
      by_contra hn
      simp [table,extendVector,hn] at hx
    refine ⟨coordinates x,?_,word_coordinates epsilon x hp⟩
    apply (hS _).mp
    simpa [table,extendVector,hp] using hx
  · rintro ⟨c,hc,rfl⟩
    rw [table_word]
    exact (hS c).mpr hc

theorem table_support_bound (omega : K) (homega : omega ≠ 0)
    (epsilon : Bool) (l : PointLabel) : (Cyclic.support (table omega epsilon l)).card ≤ 4 := by
  obtain ⟨S,hcard,hS⟩ := AtlasVectors.support_receipt omega homega l
  rw [table_support_image omega epsilon l S hS]
  exact (Finset.card_image_le).trans hcard

theorem single_support (omega : K) (homega : omega ≠ 0)
    (epsilon : Bool) (p : Block) (r : Phase) :
    Cyclic.support (table omega epsilon (single p r)) =
      {word epsilon (p,false),word epsilon (p,true)} := by
  classical
  rw [table_support_image omega epsilon (single p r) {(p,false),(p,true)}]
  · simp
  · intro c
    change singleVector omega p r c ≠ 0 ↔ _
    rw [single_support_iff omega homega]
    rcases c with ⟨q,b⟩
    cases b <;> simp

theorem single_support_card (omega : K) (homega : omega ≠ 0)
    (epsilon : Bool) (p : Block) (r : Phase) :
    (Cyclic.support (table omega epsilon (single p r))).card = 2 := by
  classical
  rw [single_support omega homega]
  have hn : word epsilon (p,false) ≠ word epsilon (p,true) := by
    intro h
    have hc := word_injective epsilon h
    have hb := congrArg Prod.snd hc
    contradiction
  simp [hn]

theorem single_support_disjoint (omega : K) (homega : omega ≠ 0)
    (epsilon : Bool) (p q : Block) (r t : Phase) (hpq : p ≠ q) :
    Disjoint (Cyclic.support (table omega epsilon (single p r)))
      (Cyclic.support (table omega epsilon (single q t))) := by
  classical
  rw [single_support omega homega,single_support omega homega]
  apply Finset.disjoint_left.mpr
  intro x hx hy
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with h | h <;>
    exact hpq (congrArg Prod.fst (word_injective epsilon h))

theorem twoBlock_support (omega : K) (homega : omega ≠ 0)
    (epsilon : Bool) (p : Pair) (r t : Phase) :
    Cyclic.support (table omega epsilon (twoBlock p r t)) =
      ({(p.1.1,false),(p.1.1,true),(p.1.2,false),(p.1.2,true)} : Finset Coordinate).image (word epsilon) := by
  classical
  apply table_support_image
  intro c
  rw [twoBlock_support_iff omega homega]
  rcases c with ⟨q,b⟩
  cases b <;> simp

theorem triangle_support_union_card (omega : K) (homega : omega ≠ 0)
    (epsilon : Bool) (t : Triple) (r : Fin 3 → Phase) :
    (Cyclic.support (table omega epsilon (twoBlock (lowerPair t) (r 0) (r 1))) ∪
      Cyclic.support (table omega epsilon (twoBlock (outerPair t) (r 0) (r 2)))).card = 6 := by
  classical
  rw [twoBlock_support omega homega,twoBlock_support omega homega,← Finset.image_union,
    Finset.card_image_of_injective _ (word_injective epsilon)]
  have hfinite : ∀ t : Triple,
      (({((lowerPair t).1.1,false),((lowerPair t).1.1,true),
        ((lowerPair t).1.2,false),((lowerPair t).1.2,true)} : Finset Coordinate) ∪
      {((outerPair t).1.1,false),((outerPair t).1.1,true),
        ((outerPair t).1.2,false),((outerPair t).1.2,true)}).card = 6 := by
    decide +kernel
  exact hfinite t

theorem support_smul (c : K) (hc : c ≠ 0) (f : Signature K 4) :
    Cyclic.support (c • f) = Cyclic.support f := by
  classical
  ext x
  simp [Cyclic.support,hc]

/-- Literal zero-or-projective atlas membership, including the twelve
one-block generalized-equality points. -/
def Admissible (omega : K) (epsilon : Bool) (f : Signature K 4) : Prop :=
  f = 0 ∨ ∃ l : PointLabel, ∃ c : K, c ≠ 0 ∧ f = c • table omega epsilon l

theorem admissible_support_bound (omega : K) (homega : omega ≠ 0)
    (epsilon : Bool) (f : Signature K 4) (hf : Admissible omega epsilon f) :
    (Cyclic.support f).card ≤ 4 := by
  classical
  rcases hf with rfl | ⟨l,c,hc,rfl⟩
  · simp [Cyclic.support]
  · rw [support_smul c hc]
    exact table_support_bound omega homega epsilon l

theorem admissible_complement_cube (omega : K) (homega : omega ^ 3 = 1)
    (epsilon : Bool) (f : Signature K 4) (hf : Admissible omega epsilon f) (x : Word4) :
    f (complement x) ^ 3 = f x ^ 3 := by
  rcases hf with rfl | ⟨l,c,hc,rfl⟩
  · simp
  · simp only [Pi.smul_apply,smul_eq_mul,mul_pow,table_complement_cube omega homega]

end
end Paper2.Certificates.DihedralSupport.AtlasParityFrame
