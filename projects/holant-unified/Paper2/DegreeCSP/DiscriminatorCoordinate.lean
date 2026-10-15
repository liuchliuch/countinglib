import Paper2.DegreeCSP.BooleanStructure

/-! A Boolean cube homomorphism for the discriminator is a constant or a
single coordinate, possibly complemented. The proof uses the actual majority
term, Boolean conjunction and disjunction, and the finite coordinate atoms.
-/
namespace Paper2.DegreeCSP.DiscriminatorCoordinate
open BooleanStructure
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
attribute [local instance] Classical.propDecidable

variable {ι : Type}

def Hom (m : Operation) (h : (ι → Bool) → Bool) : Prop :=
  ∀ x y z, h (fun i => m (x i,y i,z i)) = m (h x,h y,h z)

def zero : ι → Bool := fun _ => false
def one : ι → Bool := fun _ => true
def atom (j : ι) : ι → Bool := fun i => if i=j then true else false
def word (S : Finset ι) : ι → Bool := fun i => if i∈S then true else false

theorem majority_hom (h : (ι → Bool) → Bool) (hd : Hom discriminator h) :
    Hom majority h := by
  intro x y z
  have hm := hd x (fun i => discriminator (x i,y i,z i)) z
  rw [hd x y z] at hm
  simpa only [discriminator_majority] using hm

theorem flip_majority (a b c flip : Bool) :
    Bool.xor (majority (a,b,c)) flip =
      majority (Bool.xor a flip,Bool.xor b flip,Bool.xor c flip) := by
  cases a <;> cases b <;> cases c <;> cases flip <;> rfl

theorem constant_of_endpoints (h : (ι → Bool) → Bool) (hm : Hom majority h)
    (he : h zero = h one) : ∀ x, h x = h zero := by
  intro x
  have middle : (fun i => majority (zero i,x i,one i)) = x := by
    funext i
    cases x i <;> rfl
  have hp := hm zero x one
  rw [middle,←he] at hp
  have hv : majority (h zero,h x,h zero) = h zero := by
    cases h zero <;> cases h x <;> rfl
  exact hp.trans hv

/-- Normalization of the two endpoint values preserves the majority term. -/
theorem flip_hom (h : (ι → Bool) → Bool) (hm : Hom majority h) (flip : Bool) :
    Hom majority (fun x => Bool.xor (h x) flip) := by
  intro x y z
  change Bool.xor (h (fun i => majority (x i,y i,z i))) flip =
    majority (Bool.xor (h x) flip,Bool.xor (h y) flip,Bool.xor (h z) flip)
  rw [hm x y z]
  exact flip_majority _ _ _ _

theorem preserves_and (h : (ι → Bool) → Bool) (hm : Hom majority h)
    (hzero : h zero = false) (x y : ι → Bool) :
    h (fun i => x i && y i) = (h x && h y) := by
  have hp := hm x y zero
  have he : (fun i => majority (x i,y i,zero i)) = (fun i => x i && y i) := by
    funext i
    cases x i <;> cases y i <;> rfl
  rw [he,hzero] at hp
  have hv : majority (h x,h y,false) = (h x && h y) := by
    cases h x <;> cases h y <;> rfl
  exact hp.trans hv

theorem preserves_or (h : (ι → Bool) → Bool) (hm : Hom majority h)
    (hone : h one = true) (x y : ι → Bool) :
    h (fun i => x i || y i) = (h x || h y) := by
  have hp := hm x y one
  have he : (fun i => majority (x i,y i,one i)) = (fun i => x i || y i) := by
    funext i
    cases x i <;> cases y i <;> rfl
  rw [he,hone] at hp
  have hv : majority (h x,h y,true) = (h x || h y) := by
    cases h x <;> cases h y <;> rfl
  exact hp.trans hv

/-- If every atom of a finite set maps to false, so does its disjunction. -/
theorem false_of_atoms (h : (ι → Bool) → Bool) (hm : Hom majority h)
    (hzero : h zero = false) (hone : h one = true) (S : Finset ι)
    (ha : ∀ j∈S, h (atom j) = false) : h (word S) = false := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    have he : word (∅ : Finset ι) = zero := by funext i; simp [word,zero]
    rw [he,hzero]
  | @insert j S hj ih =>
    have he : word (insert j S) = (fun i => atom j i || word S i) := by
      funext i
      by_cases hij : i=j <;> by_cases hiS : i∈S <;> simp [word,atom,hij,hiS]
    rw [he,preserves_or h hm hone,ha j (Finset.mem_insert_self _ _),
      ih (fun i hi => ha i (Finset.mem_insert_of_mem hi))]
    rfl

/-- A normalized homomorphism must select one of the finite cube atoms. -/
theorem exists_true_atom [Fintype ι] (h : (ι → Bool) → Bool) (hm : Hom majority h)
    (hzero : h zero = false) (hone : h one = true) : ∃ j, h (atom j) = true := by
  classical
  by_contra none
  have ha : ∀ j, h (atom j) = false := by
    intro j
    cases he : h (atom j)
    · rfl
    · exact (none ⟨j,he⟩).elim
  have hp := false_of_atoms h hm hzero hone Finset.univ (fun j _ => ha j)
  have he : word (Finset.univ : Finset ι) = one := by funext i; simp [word,one]
  rw [he,hone] at hp
  cases hp

theorem coordinate_of_true_atom (h : (ι → Bool) → Bool) (hm : Hom majority h)
    (hzero : h zero = false) (j : ι) (hj : h (atom j) = true) :
    ∀ x, h x = x j := by
  intro x
  have hp := preserves_and h hm hzero (atom j) x
  rw [hj,Bool.true_and] at hp
  cases hx : x j
  · have he : (fun i => atom j i && x i) = zero := by
      funext i
      by_cases hij : i=j
      · subst i
        simp [atom,hx,zero]
      · simp [atom,hij,zero]
    rw [he,hzero] at hp
    exact hp.symm
  · have he : (fun i => atom j i && x i) = atom j := by
      funext i
      by_cases hij : i=j
      · subst i
        simp [atom,hx]
      · simp [atom,hij]
    rw [he,hj] at hp
    exact hp.symm

/-- A finite Boolean cube discriminator homomorphism is a constant or a
coordinate with one fixed Boolean flip. This also covers the empty cube. -/
theorem classify [Fintype ι] (h : (ι → Bool) → Bool) (hd : Hom discriminator h) :
    (∃ b : Bool, ∀ x, h x = b) ∨
      ∃ j : ι, ∃ flip : Bool, ∀ x, h x = Bool.xor (x j) flip := by
  have hm := majority_hom h hd
  by_cases he : h zero = h one
  · exact Or.inl ⟨h zero,constant_of_endpoints h hm he⟩
  · right
    let g : (ι → Bool) → Bool := fun x => Bool.xor (h x) (h zero)
    have hgm : Hom majority g := flip_hom h hm (h zero)
    have hgzero : g zero = false := by
      change Bool.xor (h zero) (h zero) = false
      cases h zero <;> rfl
    have hgone : g one = true := by
      change Bool.xor (h one) (h zero) = true
      cases h0 : h zero <;> cases h1 : h one <;> simp_all
    obtain ⟨j,hj⟩ := exists_true_atom g hgm hgzero hgone
    have hg := coordinate_of_true_atom g hgm hgzero j hj
    refine ⟨j,h zero,?_⟩
    intro x
    have hp := hg x
    change Bool.xor (h x) (h zero) = x j at hp
    cases h0 : h zero <;> cases hxx : h x <;> cases hjx : x j <;> simp_all

end
end Paper2.DegreeCSP.DiscriminatorCoordinate

