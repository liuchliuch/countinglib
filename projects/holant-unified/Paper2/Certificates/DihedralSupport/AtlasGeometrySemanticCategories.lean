import Paper2.Certificates.DihedralSupport.AtlasGeometrySemanticLines

/-! The four kinds count distinct actual subspaces. Their union is the
complete rich-line family, with the manuscript's fixed geometric labels. -/
namespace Paper2.Certificates.DihedralSupport.AtlasGeometrySemantic
open AtlasCounts
noncomputable section
variable {K I : Type*} [Field K]

def categoryLines {J : Type*} [Fintype J] (V : PointLabel→I→K)
    (f : J→RichLabel) : Finset (Submodule K (I→K)) := by
  classical
  exact Finset.univ.image (fun j => richLineSpace V (f j))

def oneBlockLines (V : PointLabel→I→K) :=
  categoryLines V (fun j : OneBlockLabel => (.inl j : RichLabel))
def rulingLines (V : PointLabel→I→K) :=
  categoryLines V (fun j : RulingLabel => (.inr (.inl j) : RichLabel))
def secantLines (V : PointLabel→I→K) :=
  categoryLines V (fun j : SecantLabel => (.inr (.inr (.inl j)) : RichLabel))
def triangleLines (V : PointLabel→I→K) :=
  categoryLines V (fun j : TriangleLabel => (.inr (.inr (.inr j)) : RichLabel))

theorem categoryLines_card {J : Type*} [Fintype J] (V : PointLabel→I→K)
    (hinc : ∀ r l, V l∈richLineSpace V r ↔ l∈richSet r)
    (f : J→RichLabel) (hf : Function.Injective f) :
    (categoryLines V f).card=Fintype.card J := by
  classical
  change (Finset.univ.image (richLineSpace V ∘ f)).card=Fintype.card J
  rw [Finset.card_image_of_injective _
    ((richLineSpace_injective V hinc).comp hf),Finset.card_univ]

theorem oneBlockLines_card (V : PointLabel→I→K)
    (hinc : ∀ r l, V l∈richLineSpace V r ↔ l∈richSet r) :
    (oneBlockLines V).card=4 := by
  rw [oneBlockLines,categoryLines_card V hinc _ Sum.inl_injective,oneBlock_card]

theorem rulingLines_card (V : PointLabel→I→K)
    (hinc : ∀ r l, V l∈richLineSpace V r ↔ l∈richSet r) :
    (rulingLines V).card=36 := by
  have hi : Function.Injective (fun j : RulingLabel => (.inr (.inl j) : RichLabel)) :=
    Sum.inr_injective.comp Sum.inl_injective
  rw [rulingLines,categoryLines_card V hinc _ hi,ruling_card]

theorem secantLines_card (V : PointLabel→I→K)
    (hinc : ∀ r l, V l∈richLineSpace V r ↔ l∈richSet r) :
    (secantLines V).card=54 := by
  have hi : Function.Injective (fun j : SecantLabel => (.inr (.inr (.inl j)) : RichLabel)) :=
    Sum.inr_injective.comp (Sum.inr_injective.comp Sum.inl_injective)
  rw [secantLines,categoryLines_card V hinc _ hi,secant_card]

theorem triangleLines_card (V : PointLabel→I→K)
    (hinc : ∀ r l, V l∈richLineSpace V r ↔ l∈richSet r) :
    (triangleLines V).card=108 := by
  have hi : Function.Injective (fun j : TriangleLabel => (.inr (.inr (.inr j)) : RichLabel)) :=
    Sum.inr_injective.comp (Sum.inr_injective.comp Sum.inr_injective)
  rw [triangleLines,categoryLines_card V hinc _ hi,triangle_card]

theorem richLines_categories (V : PointLabel→I→K) :
    richLines V=oneBlockLines V ∪ rulingLines V ∪ secantLines V ∪ triangleLines V := by
  classical
  ext L
  simp only [Finset.mem_union]
  constructor
  · intro h
    obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp h
    rcases r with j | j
    · exact Or.inl (Or.inl (Or.inl (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)))
    rcases j with j | j
    · exact Or.inl (Or.inl (Or.inr (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)))
    rcases j with j | j
    · exact Or.inl (Or.inr (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩))
    · exact Or.inr (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
  · intro h
    rcases h with ((h | h) | h) | h
    all_goals
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩

end
end Paper2.Certificates.DihedralSupport.AtlasGeometrySemantic

