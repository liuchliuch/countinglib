import Paper2.Tractable.Affine
import Paper2.Tractable.Product
import Mathlib.Data.Finset.Card

/-! Boolean specialization of the actual common-support Mal'tsev conclusion.
The operation conventions are the literal definitions in
ComplexCSP/Structure/MaltsevRelations.lean. These are pure finite algebra lemmas;
no hardness, runtime classification, or degree-generated closure is postulated. -/
namespace Paper2.DegreeCSP.BooleanStructure
noncomputable section

abbrev Operation := Bool × Bool × Bool → Bool

def IsMaltsev (m : Operation) : Prop :=
  (∀ a b, m (a,b,b) = a) ∧ (∀ a b, m (b,b,a) = a)

def Preserves {ι : Type} (m : Operation) (R : Set (ι → Bool)) : Prop :=
  ∀ x ∈ R, ∀ y ∈ R, ∀ z ∈ R, (fun i => m (x i,y i,z i)) ∈ R

def xor3 : Operation := fun p => Bool.xor (Bool.xor p.1 p.2.1) p.2.2

def discriminator : Operation := fun p => if p.1 = p.2.1 then p.2.2 else p.1

def majority : Operation := fun p => if p.1 = p.2.1 then p.1 else p.2.2

def disequalityRelation : Set (Fin 2 → Bool) := {x | x 0 ≠ x 1}

/-- Preserving the actual binary disequality forces complement equivariance. -/
theorem preserves_disequality_complement (m : Operation)
    (hm : Preserves m disequalityRelation) (a b c : Bool) :
    m (!a,!b,!c) = !(m (a,b,c)) := by
  have h := hm ![a,!a] (by cases a <;> simp [disequalityRelation])
    ![b,!b] (by cases b <;> simp [disequalityRelation])
    ![c,!c] (by cases c <;> simp [disequalityRelation])
  change m (a,b,c) ≠ m (!a,!b,!c) at h
  cases h0 : m (a,b,c) <;> cases h1 : m (!a,!b,!c) <;> simp_all

/-- There are exactly two Boolean Mal'tsev operations that preserve X. -/
theorem maltsev_classification (m : Operation) (hm : IsMaltsev m)
    (hX : Preserves m disequalityRelation) : m = xor3 ∨ m = discriminator := by
  have hcomp := preserves_disequality_complement m hX false true false
  cases h : m (false,true,false)
  · right
    have ht : m (true,false,true) = true := by simpa [h] using hcomp
    funext p
    rcases p with ⟨a,b,c⟩
    cases a <;> cases b <;> cases c <;>
      simp_all [discriminator,IsMaltsev]
  · left
    have ht : m (true,false,true) = false := by simpa [h] using hcomp
    funext p
    rcases p with ⟨a,b,c⟩
    cases a <;> cases b <;> cases c <;>
      simp_all [xor3,IsMaltsev]

/-- A composed discriminator term is the Boolean majority operation. -/
theorem discriminator_majority (a b c : Bool) :
    discriminator (a,discriminator (a,b,c),c) = majority (a,b,c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem preserves_majority {ι : Type} {R : Set (ι → Bool)}
    (hR : Preserves discriminator R) : Preserves majority R := by
  intro x hx y hy z hz
  have ht := hR x hx y hy z hz
  have hu := hR x hx (fun i => discriminator (x i,y i,z i)) ht z hz
  simpa only [discriminator_majority] using hu

/-- At every coordinate, any two equal inputs fix the majority value. -/
theorem majority_eq (a b c t : Bool) (h : (a=t ∧ b=t) ∨ (a=t ∧ c=t) ∨ (b=t ∧ c=t)) :
    majority (a,b,c) = t := by
  rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> simp [majority]

/-- Three supported rows matching all but three distinct coordinates combine
into one row matching every inspected coordinate. -/
theorem merge_three {ι : Type} [DecidableEq ι] (R : Set (ι → Bool))
    (hR : Preserves majority R) (S : Finset ι) (x : ι → Bool)
    (a b c : ι) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (u v w : ι → Bool) (hu : u ∈ R) (hv : v ∈ R) (hw : w ∈ R)
    (hU : ∀ i ∈ S.erase a, u i = x i)
    (hV : ∀ i ∈ S.erase b, v i = x i)
    (hW : ∀ i ∈ S.erase c, w i = x i) :
    ∃ z ∈ R, ∀ i ∈ S, z i = x i := by
  refine ⟨fun i => majority (u i,v i,w i),hR u hu v hv w hw,?_⟩
  intro i hi
  apply majority_eq
  by_cases hia : i = a
  · subst i
    exact Or.inr (Or.inr ⟨hV a (Finset.mem_erase.mpr ⟨hab,hi⟩),
      hW a (Finset.mem_erase.mpr ⟨hac,hi⟩)⟩)
  · by_cases hib : i = b
    · subst i
      exact Or.inr (Or.inl ⟨hU b (Finset.mem_erase.mpr ⟨hab.symm,hi⟩),
        hW b (Finset.mem_erase.mpr ⟨hbc,hi⟩)⟩)
    · exact Or.inl ⟨hU i (Finset.mem_erase.mpr ⟨hia,hi⟩),
        hV i (Finset.mem_erase.mpr ⟨hib,hi⟩)⟩

/-- A majority-closed nonempty relation is determined by its unary and binary
projections. The witnesses are actual rows of the relation. -/
theorem pairwise_reconstruct {ι : Type} [Fintype ι] [DecidableEq ι]
    (R : Set (ι → Bool)) (hne : R.Nonempty) (hR : Preserves majority R)
    (x : ι → Bool)
    (hp : ∀ i j : ι, ∃ z ∈ R, z i = x i ∧ z j = x j) : x ∈ R := by
  classical
  have extension : ∀ n : ℕ, ∀ S : Finset ι, S.card = n →
      ∃ z ∈ R, ∀ i ∈ S, z i = x i := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro S hcard
      by_cases hsmall : S.card ≤ 2
      · by_cases hempty : S = ∅
        · obtain ⟨z,hz⟩ := hne
          exact ⟨z,hz,by simp [hempty]⟩
        · obtain ⟨a,ha⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
          have hpos : 0 < S.card := Finset.card_pos.mpr ⟨a,ha⟩
          by_cases hone : S.card = 1
          · obtain ⟨z,hz,hza,_⟩ := hp a a
            refine ⟨z,hz,?_⟩
            intro i hi
            have hia : i = a := by
              have hs := Finset.card_le_one.mp (by omega : S.card ≤ 1) i hi a ha
              exact hs
            simpa only [hia] using hza
          · have hecard : (S.erase a).card = 1 := by
              rw [Finset.card_erase_of_mem ha]
              omega
            obtain ⟨b,hb⟩ := Finset.card_eq_one.mp hecard
            obtain ⟨z,hz,hza,hzb⟩ := hp a b
            refine ⟨z,hz,?_⟩
            intro i hi
            by_cases hia : i = a
            · simpa only [hia] using hza
            · have hib : i = b := by
                have hh := Finset.mem_erase.mpr ⟨hia,hi⟩
                rw [hb] at hh
                simpa using hh
              simpa only [hib] using hzb
      · obtain ⟨a,ha⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
        have hea : (S.erase a).Nonempty := by
          apply Finset.card_pos.mp
          rw [Finset.card_erase_of_mem ha]
          omega
        obtain ⟨b,hb⟩ := hea
        obtain ⟨hab',hbS⟩ := Finset.mem_erase.mp hb
        have heb : ((S.erase a).erase b).Nonempty := by
          apply Finset.card_pos.mp
          rw [Finset.card_erase_of_mem hb,Finset.card_erase_of_mem ha]
          omega
        obtain ⟨c,hc⟩ := heb
        obtain ⟨hcb,hcA⟩ := Finset.mem_erase.mp hc
        obtain ⟨hca,hcS⟩ := Finset.mem_erase.mp hcA
        obtain ⟨u,hu,hU⟩ := ih (S.erase a).card (by rw [Finset.card_erase_of_mem ha]; omega) _ rfl
        obtain ⟨v,hv,hV⟩ := ih (S.erase b).card (by rw [Finset.card_erase_of_mem hbS]; omega) _ rfl
        obtain ⟨w,hw,hW⟩ := ih (S.erase c).card (by rw [Finset.card_erase_of_mem hcS]; omega) _ rfl
        exact merge_three R hR S x a b c hab'.symm hca.symm hcb.symm u v w hu hv hw hU hV hW
  obtain ⟨z,hz,hmatch⟩ := extension Finset.univ.card Finset.univ rfl
  have he : z = x := by funext i; exact hmatch i (Finset.mem_univ i)
  exact he ▸ hz

end
end Paper2.DegreeCSP.BooleanStructure
