import ComplexCSP.Algebra.PositiveGramPowerField

/-! # Selecting the actual numerical support component of a Gram obstruction

The component is positive-edge reachability. With nonnegative entries this is
exactly nonzero support reachability; its proved closure has the literal form
of the support-restriction machine's ColorClosed premise.
-/
noncomputable section
open Classical
namespace ComplexCSP.PositiveGramComponent
open scoped BigOperators
variable {I C : Type} [Fintype C]
variable (K : IntermediateField ℚ ℝ) (A : Matrix I I K)

def component (i : I) : Set I :=
  {j | Relation.ReflTransGen (fun x y => 0<A x y) i j}

theorem root_mem (i : I) : i∈component K A i := Relation.ReflTransGen.refl

theorem adjacent_mem (i j : I) (hij : 0<A i j) : j∈component K A i :=
  Relation.ReflTransGen.single hij

/-- This proposition is definitionally PlanarHom.RootedRestriction.ColorClosed;
it is proved without importing any extra vendor graph machinery. -/
theorem colorClosed (hA : ∀ i j,0≤A i j) (i : I) :
    ∀ x ∈ component K A i,∀ y,A x y≠0 → y∈component K A i := by
  intro x hx y hxy
  exact Relation.ReflTransGen.tail hx (lt_of_le_of_ne (hA x y) (Ne.symm hxy))

private theorem lift_path (i : I)
    (hclosed : ∀ x ∈ component K A i,∀ y,0<A x y → y∈component K A i)
    {x y : I} (hx : x∈component K A i)
    (hxy : Relation.ReflTransGen (fun x y => 0<A x y) x y) :
    ∃ hy : y∈component K A i,
      Relation.ReflTransGen (fun u v : component K A i => 0<A u.val v.val) ⟨x,hx⟩ ⟨y,hy⟩ := by
  induction hxy with
  | refl => exact ⟨hx,Relation.ReflTransGen.refl⟩
  | @tail y z hxy hyz ih =>
    obtain ⟨hy,hpath⟩ := ih
    exact ⟨hclosed y hy z hyz,Relation.ReflTransGen.tail hpath hyz⟩

private theorem reverse_path (hs : ∀ i j,A i j=A j i) {i j : I}
    (h : Relation.ReflTransGen (fun x y => 0<A x y) i j) :
    Relation.ReflTransGen (fun x y => 0<A x y) j i := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail hab hbc ih =>
    exact (Relation.ReflTransGen.single (by rwa [hs] at hbc)).trans ih

/-- Every two colors in the chosen numerical component are positively connected
inside the literal restricted index subtype. -/
theorem connected (hs : ∀ i j,A i j=A j i) (i : I) :
    ∀ x y : component K A i,
      Relation.ReflTransGen (fun u v : component K A i => 0<A u.val v.val) x y := by
  intro x y
  have hx : Relation.ReflTransGen (fun u v => 0<A u v) x.val i :=
    reverse_path K A hs x.property
  have hpath := hx.trans y.property
  have hclosed : ∀ x ∈ component K A i,∀ y,0<A x y → y∈component K A i :=
    fun x hx y hxy => Relation.ReflTransGen.tail hx hxy
  obtain ⟨hy,hh⟩ := lift_path K A i hclosed x.property hpath
  exact hh

/-- The Gram identity, rather than an assumed positive-diagonal property,
forces every selected component diagonal to be positive. -/
theorem diagonal_positive (B : I → C → ℝ) (hB : ∀ i z,0≤B i z)
    (hGram : ∀ i j,(A i j : ℝ)=∑ z,B i z*B j z)
    (i : I) (hii : 0<A i i) : ∀ x : component K A i,0<A x.val x.val := by
  intro x
  have hi : 0<GramObstruction.gram B i i := by rw [GramObstruction.gram,←hGram]; exact hii
  have hpath : Relation.ReflTransGen (fun u v => 0<GramObstruction.gram B u v) i x.val := by
    refine Relation.ReflTransGen.mono ?_ i x.val x.property
    intro u v huv
    rw [GramObstruction.gram,←hGram]
    exact huv
  have h := PositiveGramPower.gram_diagonal_on_component B hB hi hpath
  change 0<(A x.val x.val : ℝ)
  rw [hGram]
  exact h

/-- The actual pair from the strict principal minor lies in the chosen component
and retains all four strict-minor inequalities after restriction. -/
theorem restricted_minor (i j : I) (hm : PositiveGramPowerField.StrictMinor K A i j) :
    let hi := root_mem K A i
    let hj := adjacent_mem K A i j hm.2.1
    PositiveGramPowerField.StrictMinor K (fun x y : component K A i => A x.val y.val)
      ⟨i,hi⟩ ⟨j,hj⟩ := hm

/-- Direct packaged component choice for the remaining BG positive-core route. -/
theorem selected_component (hA : ∀ i j,0≤A i j) (hs : ∀ i j,A i j=A j i)
    (B : I → C → ℝ) (hB : ∀ i z,0≤B i z)
    (hGram : ∀ i j,(A i j : ℝ)=∑ z,B i z*B j z)
    (i j : I) (hm : PositiveGramPowerField.StrictMinor K A i j) :
    (∀ x ∈ component K A i,∀ y,A x y≠0 → y∈component K A i) ∧
    j∈component K A i ∧
    (∀ x : component K A i,0<A x.val x.val) ∧
    (∀ x y : component K A i,
      Relation.ReflTransGen (fun u v : component K A i => 0<A u.val v.val) x y) :=
  ⟨colorClosed K A hA i,adjacent_mem K A i j hm.2.1,
    diagonal_positive K A B hB hGram i hm.1,connected K A hs i⟩

end ComplexCSP.PositiveGramComponent
