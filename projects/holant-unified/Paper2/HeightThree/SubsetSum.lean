import Paper2.HeightThree.CardGeometry

/-! An explicit bijection between the sixteen internal edge assignments and
subsets of the four internal source ports. -/
namespace Paper2.HeightThree
open Certificates.Q6
open scoped BigOperators
noncomputable section

abbrev internalDomain (s : CardSpec) : PortSet := internalLeft s

def occupiedInternal (s : CardSpec) (z : LeftInterior s → Bool) : PortSet :=
  (Finset.univ.filter (fun v => z v = true)).image Subtype.val

def internalAssignment (s : CardSpec) (T : PortSet) : LeftInterior s → Bool :=
  fun v => decide (v.val ∈ T)

lemma occupiedInternal_subset (s : CardSpec) (z : LeftInterior s → Bool) :
    occupiedInternal s z ⊆ internalLeft s := by
  intro v hv
  obtain ⟨u,_,rfl⟩ := Finset.mem_image.mp hv
  exact u.property

lemma mem_occupiedInternal (s : CardSpec) (z : LeftInterior s → Bool) (v : LeftInterior s) :
    v.val ∈ occupiedInternal s z ↔ z v = true := by
  simp only [occupiedInternal,Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨u,hu,h⟩
    have huv : u = v := Subtype.ext h
    rwa [huv] at hu
  · intro h
    exact ⟨v,h,rfl⟩

lemma internalAssignment_occupied (s : CardSpec) (z : LeftInterior s → Bool) :
    internalAssignment s (occupiedInternal s z) = z := by
  funext v
  simp only [internalAssignment,mem_occupiedInternal,Bool.decide_eq_true]

lemma occupiedInternal_assignment (s : CardSpec) (T : PortSet) (hT : T ⊆ internalLeft s) :
    occupiedInternal s (internalAssignment s T) = T := by
  ext v
  constructor
  · intro hv
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
    have hh := (Finset.mem_filter.mp hu).2
    exact of_decide_eq_true hh
  · intro hv
    refine Finset.mem_image.mpr ⟨⟨v,hT hv⟩,?_,rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,decide_eq_true hv⟩

lemma occupiedInternal_injective (s : CardSpec) : Function.Injective (occupiedInternal s) := by
  intro z w h
  have hh := congrArg (internalAssignment s) h
  simpa only [internalAssignment_occupied] using hh

lemma sum_internal_subsets {K : Type*} [AddCommMonoid K] (s : CardSpec) (f : PortSet → K) :
    (∑ z : LeftInterior s → Bool, f (occupiedInternal s z)) =
      ∑ T ∈ (internalLeft s).powerset, f T := by
  apply Finset.sum_bij (fun z _ => occupiedInternal s z)
  · intro z _
    exact Finset.mem_powerset.mpr (occupiedInternal_subset s z)
  · intro z _ w _ h
    exact occupiedInternal_injective s h
  · intro T hT
    exact ⟨internalAssignment s T,Finset.mem_univ _,
      occupiedInternal_assignment s T (Finset.mem_powerset.mp hT)⟩
  · intro z _
    rfl

end
end Paper2.HeightThree
