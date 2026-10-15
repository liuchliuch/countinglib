import Paper2.SourceFaithful.SourceStatements.OddDihedralPencilAlgebra
import Paper2.SourceFaithful.SourceStatements.OddDihedralTwoBlockSeed

/-! A secant pencil has a literal eight-word matching-cube support.  The
argument permits two-word generalized-equality cards throughout. -/
namespace Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion
open Paper2.HeightOne Paper2.HeightOne.Dihedral
open SixPortSupport SixPortPencils
noncomputable section
set_option maxRecDepth 4096

variable {K : Type} [Field K]
local instance {α : Type*} : DecidableEq α := Classical.decEq α

def sixComplement (x : Word6) : Word6 := fun i => !(x i)

theorem sixComplement_lift (p : Equiv.Perm (Fin 6)) (xi b : Bool) (r : Word4) :
    sixComplement (lift p xi b r) = lift p xi (!b) (complement r) := by
  have he : (fun i => !(extend xi b r i)) = extend xi (!b) (complement r) := by
    funext i
    refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun l => rfl) j) i
    · simp [extend]
    · cases xi <;> cases b <;> rfl
  funext i
  exact congrFun he (p.symm i)

theorem two_word_complement_pair (U : Finset Word4) (hcard : U.card = 2)
    (hcomp : ∀ x ∈ U, complement x ∈ U) :
    ∃ a : Word4, U = {a,complement a} := by
  classical
  obtain ⟨a,ha⟩ := Finset.card_pos.mp (show 0 < U.card by omega)
  refine ⟨a, (Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
  · intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    · rw [Finset.mem_singleton] at hx
      exact hx ▸ hcomp a ha
  · simp [hcard, (complement_ne a).symm]

theorem joint_union_two_phases {X : Type*} [Fintype X]
    (A B : X → K) (s t : K) (hst : s ≠ t) :
    jointSupport A B = pencilSupport A B s ∪ pencilSupport A B t := by
  classical
  ext x
  simp only [mem_jointSupport, Finset.mem_union, mem_pencilSupport]
  constructor
  · intro hx
    by_contra hn
    push Not at hn
    have hB : B x ≠ 0 := by
      intro hz
      have ha : A x = 0 := by simpa [hz] using hn.1
      exact hx.elim (fun h => h ha) (fun h => h hz)
    have he : s * B x = t * B x :=
      (sub_eq_zero.mp hn.1).symm.trans (sub_eq_zero.mp hn.2)
    exact hst (mul_right_cancel₀ hB he)
  · intro hx
    by_contra hn
    push Not at hn
    rcases hx with h | h <;> exact h (by simp [hn.1, hn.2])

theorem disjoint_two_word_joint (A B : Word4 → K) (s t : K)
    (hst : s ≠ t)
    (hs : (pencilSupport A B s).card = 2)
    (ht : (pencilSupport A B t).card = 2)
    (hdis : Disjoint (pencilSupport A B s) (pencilSupport A B t))
    (hcomps : ∀ x ∈ pencilSupport A B s, complement x ∈ pencilSupport A B s)
    (hcompt : ∀ x ∈ pencilSupport A B t, complement x ∈ pencilSupport A B t) :
    ∃ a b : Word4, a ≠ b ∧ b ≠ complement a ∧
      jointSupport A B = twoBlocks a b := by
  classical
  obtain ⟨a,ha⟩ := two_word_complement_pair _ hs hcomps
  obtain ⟨b,hb⟩ := two_word_complement_pair _ ht hcompt
  have hdis' := hdis
  rw [ha, hb] at hdis'
  have hne : a ≠ b := by
    intro h
    exact (Finset.disjoint_left.mp hdis') (by simp : a ∈ ({a,complement a} : Finset Word4))
      (by simp [h] : a ∈ ({b,complement b} : Finset Word4))
  have hbc : b ≠ complement a := by
    intro h
    exact (Finset.disjoint_left.mp hdis') (by simp : complement a ∈ _) (by simp [h])
  refine ⟨a,b,hne,hbc,?_⟩
  rw [joint_union_two_phases A B s t hst,ha,hb]
  ext x
  simp [twoBlocks,or_left_comm,or_comm]

theorem secant_support_is_seed (f : Signature K 6) (hpar : HasParity f)
    (xi : Bool) (s t : K) (hst : s ≠ t) (hs0 : s ≠ 0) (ht0 : t ≠ 0)
    (hs : (pencilSupport (first f (Equiv.refl _) xi)
      (second f (Equiv.refl _) xi) s).card = 2)
    (ht : (pencilSupport (first f (Equiv.refl _) xi)
      (second f (Equiv.refl _) xi) t).card = 2)
    (hdis : Disjoint
      (pencilSupport (first f (Equiv.refl _) xi) (second f (Equiv.refl _) xi) s)
      (pencilSupport (first f (Equiv.refl _) xi) (second f (Equiv.refl _) xi) t))
    (hcomps : ∀ x ∈ pencilSupport (first f (Equiv.refl _) xi) (second f (Equiv.refl _) xi) s,
      complement x ∈ pencilSupport (first f (Equiv.refl _) xi) (second f (Equiv.refl _) xi) s)
    (hcompt : ∀ x ∈ pencilSupport (first f (Equiv.refl _) xi) (second f (Equiv.refl _) xi) t,
      complement x ∈ pencilSupport (first f (Equiv.refl _) xi) (second f (Equiv.refl _) xi) t)
    (hbound : ∀ p eta, (sector (support f) p eta).card ≤ 4) :
    ∃ a b : Word4, a ≠ b ∧ b ≠ complement a ∧ parity a = parity b ∧
      support f = twoBlockSeed a b xi := by
  classical
  obtain ⟨a,b,hab,hbc,hjoint⟩ := disjoint_two_word_joint _ _ s t hst hs ht hdis hcomps hcompt
  have hsector : sector (support f) (Equiv.refl _) xi = twoBlocks a b := by
    rwa [joint_sector] at hjoint
  have hp : parity a = parity b := sector_parity f hpar (Equiv.refl (Fin 6)) xi a (by simp [hsector,twoBlocks])
    b (by simp [hsector,twoBlocks])
  have hcomplete : CompleteSector (support f) (Equiv.refl _) xi := by
    intro r hr z
    rw [← joint_sector] at hr
    have hn := disjoint_pencils_source_nonzero _ _ s t hs0 ht0 hdis r hr
    cases z
    · simpa [support,first] using hn.1
    · simpa [support,second] using hn.2
  have hseed : twoBlockSeed a b xi ⊆ support f := by
    intro x hx
    obtain ⟨hxi,hr⟩ : (x 0 ^^ x 1) = xi ∧ residual x ∈ twoBlocks a b := by
      simpa [twoBlockSeed] using hx
    have hmem := hcomplete (residual x) (by rwa [hsector]) (x 0)
    have he : lift (Equiv.refl _) xi (x 0) (residual x) = x := by
      rw [← hxi]
      simpa using lift_residual (Equiv.refl (Fin 6)) x
    rwa [he] at hmem
  have hhead := two_block_seed_no_opposite a b xi hab hbc hp _ hseed hbound
  refine ⟨a,b,hab,hbc,hp,Finset.Subset.antisymm ?_ hseed⟩
  intro x hx
  have hh := hhead x hx
  have hr : residual x ∈ sector (support f) (Equiv.refl _) xi := by
    apply (mem_sector _ _ _ _).mpr
    refine ⟨x 0,?_⟩
    have he : lift (Equiv.refl _) xi (x 0) (residual x) = x := by
      rw [← hh]
      simpa using lift_residual (Equiv.refl (Fin 6)) x
    rwa [he]
  simpa [twoBlockSeed,hsector,hh] using hr

end
end Paper2.SourceFaithful.SourceStatements.OddDihedralPencilExclusion
