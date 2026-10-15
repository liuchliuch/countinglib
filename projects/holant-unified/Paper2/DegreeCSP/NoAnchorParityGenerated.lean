import Paper2.DegreeCSP.NoAnchorWeightedParity
import Paper2.DegreeCSP.BooleanAffineParityMinor
import Paper2.DegreeCSP.GeneratedPins

/-! A nonproduct affine support gives an actual weighted parity face in the
no-anchor branch. Pins fix the other live coordinates. The genuine marginal
then has a unique nonzero source fiber, retaining its original coefficient. -/
namespace Paper2.DegreeCSP.NoAnchorParityGenerated
open scoped BigOperators
open Tractable TensorDecomposition NoAnchorWeightedSupport BooleanAffineParityMinor
open GeneratedCoordinateMarginal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
attribute [local instance] Classical.propDecidable

variable {F : SignatureFamily AlgebraicComplex} {k n r : ℕ}

def remaining (i j : Fin r) : Finset (Fin r) := Finset.univ.erase i |>.erase j

theorem mem_remaining (i j l : Fin r) : l∈remaining i j ↔ l≠i ∧ l≠j := by
  simp [remaining,and_comm]

def pinnedTable (f : Signature AlgebraicComplex n) (a : Fin n→Bool)
    (q : Fin r→Fin n) (i j : Fin r) : Signature AlgebraicComplex n :=
  fun x=>if Pinned a q i j x then f x else 0

theorem pinnedTable_ne_zero (f : Signature AlgebraicComplex n) (a : Fin n→Bool)
    (q : Fin r→Fin n) (i j : Fin r) (x : Fin n→Bool) :
    pinnedTable f a q i j x≠0 ↔ f x≠0 ∧ Pinned a q i j x := by
  by_cases hp : Pinned a q i j x <;> simp [pinnedTable,hp]

theorem pinnedTable_generated (f : Signature AlgebraicComplex n)
    (hf : Generated F k f) (hp : ∀b,Generated F k (literalPin b))
    (a : Fin n→Bool) (q : Fin r→Fin n) (i j : Fin r) :
    Generated F k (pinnedTable f a q i j) := by
  classical
  let g : Fin r→Signature AlgebraicComplex n :=
    fun l x=>literalPin (a (q l)) (fun _=>x (q l))
  have hg (l : Fin r) : Generated F k (g l) :=
    generated_pullback (hp (a (q l))) (fun _ : Fin 1=>q l)
  have hprod (s : Finset (Fin r)) : Generated F k (fun x=>∏l∈s,g l x) := by
    induction s using Finset.induction_on with
    | empty => simpa using generated_one F k n
    | @insert l s hl ih =>
      simpa only [Finset.prod_insert hl] using generated_hadamard (hg l) ih
  convert generated_hadamard hf (hprod (remaining i j)) using 1
  funext x
  have he : (∀l∈remaining i j,x (q l)=a (q l)) ↔ Pinned a q i j x := by
    constructor
    · intro h l hli hlj
      exact h l ((mem_remaining i j l).mpr ⟨hli,hlj⟩)
    · intro h l hl
      exact h l ((mem_remaining i j l).mp hl).1 ((mem_remaining i j l).mp hl).2
  simp only [g,literalPin,Finset.prod_boole,he]
  unfold pinnedTable
  split_ifs <;> simp

def coordinates (q : Fin r→Fin n) (i j : Fin r) (t : Fin n) : Fin 3→Fin n :=
  ![q i,q j,t]

theorem coordinates_injective (q : Fin r→Fin n) (hq : Function.Injective q)
    (i j : Fin r) (hij : i≠j) (t : Fin n) (hti : t≠q i) (htj : t≠q j) :
    Function.Injective (coordinates q i j t) := by
  intro u v huv
  have hqij : q i≠q j := fun h=>hij (hq h)
  fin_cases u <;> fin_cases v <;> simp_all [coordinates,Ne.symm]

theorem pinned_projection_injective (f : Signature AlgebraicComplex n)
    (a : Fin n→Bool) (q : Fin r→Fin n)
    (hq : Function.Injective (liveProjection f q)) (i j : Fin r) (t : Fin n) :
    Function.Injective (liveProjection (pinnedTable f a q i j) (coordinates q i j t)) := by
  intro x y hxy
  have hx := (pinnedTable_ne_zero f a q i j x.val).mp x.property
  have hy := (pinnedTable_ne_zero f a q i j y.val).mp y.property
  apply Subtype.ext
  apply pinned_projection_unique_relation {x | f x≠0} a q hq i j
    (fun l=>x.val (coordinates q i j t l)) x.val y.val hx.1 hy.1
  · rfl
  · exact (congrFun hxy 0).symm
  · rfl
  · exact (congrFun hxy 1).symm
  · exact hx.2
  · exact hy.2

theorem product_pinned (u : Fin r→Bool→AlgebraicComplex) (a : Fin n→Bool)
    (q : Fin r→Fin n) (i j : Fin r) (hij : i≠j) (x : Fin n→Bool)
    (hp : Pinned a q i j x) :
    (∏l,u l (x (q l))) =
      (∏l∈remaining i j,u l (a (q l)))*u i (x (q i))*u j (x (q j)) := by
  classical
  have he : (∏l∈remaining i j,u l (x (q l))) =
      ∏l∈remaining i j,u l (a (q l)) := by
    apply Finset.prod_congr rfl
    intro l hl
    rw [hp l ((mem_remaining i j l).mp hl).1 ((mem_remaining i j l).mp hl).2]
  have hji : j∈(Finset.univ : Finset (Fin r)).erase i := by simp [hij.symm]
  have h1 := Finset.prod_erase_mul (Finset.univ : Finset (Fin r))
    (fun l=>u l (x (q l))) (Finset.mem_univ i)
  have h2 := Finset.prod_erase_mul ((Finset.univ : Finset (Fin r)).erase i)
    (fun l=>u l (x (q l))) hji
  change (∏l∈remaining i j,u l (x (q l)))*u j (x (q j)) = _ at h2
  rw [←h1,←h2,he]
  ring

/-- The exact same live-coordinate marginal that supplies the product weights
also supplies the parity minor. Its four fibers have no multiplicity. -/
theorem exists_weighted_parity (hno : AllFullSupportProduct F k)
    (hp : ∀b,Generated F k (literalPin b))
    (f : Signature AlgebraicComplex n) (hf : Generated F k f)
    (a : Fin n→Bool) (ha : f a≠0)
    (hxor : BooleanStructure.Preserves BooleanStructure.xor3 {x | f x≠0})
    (hnon : ¬Product (BooleanStructure.indicator {x | f x≠0})) :
    ∃ (A B : Bool→AlgebraicComplex) (offset : Bool),
      (∀b,A b≠0) ∧ (∀b,B b≠0) ∧
        Generated F k (NoAnchorWeightedParity.table A B offset) := by
  classical
  obtain ⟨r,q,hq,hproj⟩ := AffineLiveCoordinates.exists_live_coordinates_xor f a ha hxor
  obtain ⟨h,hh,hhne,hcoeff⟩ := generated_coordinate_marginal f hf q hq hproj
  obtain ⟨c,u,hc,hu,hform⟩ := FullSupportProduct.unary_factorization h (hno r h hh hhne) hhne
  obtain ⟨i,j,t,hij,hti,htj,hpar⟩ :=
    exists_parity_minor_on_coordinates {x | f x≠0} a ha hxor hnon q hproj
  let C : AlgebraicComplex := c*∏l∈remaining i j,u l (a (q l))
  let A : Bool→AlgebraicComplex := fun b=>C*u i b
  let B : Bool→AlgebraicComplex := u j
  let offset := Bool.xor (Bool.xor (a (q i)) (a (q j))) (a t)
  have hC : C≠0 := mul_ne_zero hc (Finset.prod_ne_zero_iff.mpr (fun l _=>hu l _))
  have hA : ∀b,A b≠0 := fun b=>mul_ne_zero hC (hu i b)
  let p := pinnedTable f a q i j
  let q3 := coordinates q i j t
  have hq3 : Function.Injective q3 := coordinates_injective q hq i j hij t hti htj
  have hproj3 : Function.Injective (liveProjection p q3) :=
    pinned_projection_injective f a q hproj.1 i j t
  have hg : Generated F k (GeneratedCoordinateMarginal.marginal p q3) :=
    generated_marginal p (pinnedTable_generated f hf hp a q i j) q3
  have he : GeneratedCoordinateMarginal.marginal p q3=
      NoAnchorWeightedParity.table A B offset := by
    funext z
    by_cases hz : z 2=Bool.xor (Bool.xor (z 0) (z 1)) offset
    · obtain ⟨x,hx,hxi,hxj,hxt,hxp⟩ := (hpar z).mpr hz
      have hpx : p x≠0 := (pinnedTable_ne_zero f a q i j x).mpr ⟨hx,hxp⟩
      have hword : (fun l=>x (q3 l))=z := by
        funext l
        fin_cases l <;> assumption
      have hm := marginal_at_live p q3 hq3 hproj3 x hpx
      rw [hword] at hm
      rw [hm,NoAnchorWeightedParity.table,ite_eq_left hz]
      change pinnedTable f a q i j x=A (z 0)*B (z 1)
      rw [pinnedTable,ite_eq_left hxp,←hcoeff x hx,hform,
        product_pinned u a q i j hij x hxp,hxi,hxj]
      dsimp [A,B,C]
      ring
    · rw [NoAnchorWeightedParity.table,ite_eq_right hz]
      apply Finset.sum_eq_zero
      intro b _
      change p (assignment q3 z b)=0
      by_contra hn
      have hs := (pinnedTable_ne_zero f a q i j (assignment q3 z b)).mp hn
      have hpp : PinnedProjection {x | f x≠0} a q i j t z := by
        refine ⟨assignment q3 z b,hs.1,?_,?_,?_,hs.2⟩
        · exact assignment_selected q3 hq3 z b 0
        · exact assignment_selected q3 hq3 z b 1
        · exact assignment_selected q3 hq3 z b 2
      exact hz ((hpar z).mp hpp)
  exact ⟨A,B,offset,hA,hu j,he ▸ hg⟩

end
end Paper2.DegreeCSP.NoAnchorParityGenerated
