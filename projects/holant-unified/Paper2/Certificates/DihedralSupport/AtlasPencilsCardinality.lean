import Paper2.Certificates.DihedralSupport.AtlasPencils
import Paper2.Certificates.DihedralSupport.AtlasCountsIncidence

/-! Cardinalities of actual projective objects. The geometric hypotheses
refer to literal vectors and nonzero minors; they are supplied by the exact
atlas geometry certificate. The counted pencil classes identify exactly one
common nonzero scalar multiplying both coefficient vectors. -/
namespace Paper2.Certificates.DihedralSupport.AtlasPencils
open AtlasGeometry AtlasCounts
noncomputable section
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 10000

variable {K : Type*} [Field K] {I : Type*}

def ScaleEquivalent (u v : I → K) : Prop := ∃ c : K, c ≠ 0 ∧ v = c • u

def vectorSetoid : Setoid (I → K) where
  r := ScaleEquivalent
  iseqv := by
    refine ⟨?_,?_,?_⟩
    · intro u
      exact ⟨1,one_ne_zero,by simp⟩
    · rintro u v ⟨c,hc,hv⟩
      refine ⟨c⁻¹,inv_ne_zero hc,?_⟩
      rw [hv,smul_smul,inv_mul_cancel₀ hc,one_smul]
    · rintro u v w ⟨c,hc,hv⟩ ⟨d,hd,hw⟩
      exact ⟨d*c,mul_ne_zero hd hc,by rw [hw,hv,smul_smul]⟩

abbrev PointClass (K I : Type*) [Field K] := Quotient (vectorSetoid (K := K) (I := I))
def pointClass (v : I → K) : PointClass K I := Quotient.mk _ v

def pencilSetoid : Setoid (Pencil K I) where
  r := Equivalent
  iseqv := by
    refine ⟨?_,?_,?_⟩
    · intro P
      exact ⟨1,one_ne_zero,by simp,by simp⟩
    · rintro P Q ⟨c,hc,hA,hB⟩
      refine ⟨c⁻¹,inv_ne_zero hc,?_,?_⟩
      · rw [hA,smul_smul,inv_mul_cancel₀ hc,one_smul]
      · rw [hB,smul_smul,inv_mul_cancel₀ hc,one_smul]
    · rintro P Q R ⟨c,hc,hA,hB⟩ ⟨d,hd,hRA,hRB⟩
      exact ⟨d*c,mul_ne_zero hd hc,
        by rw [hRA,hA,smul_smul],by rw [hRB,hB,smul_smul]⟩

abbrev PencilClass (K I : Type*) [Field K] := Quotient (pencilSetoid (K := K) (I := I))
def pencilClass (P : Pencil K I) : PencilClass K I := Quotient.mk _ P

def AtlasIndependent (V : PointLabel → I → K) : Prop :=
  ∀ p q, p ≠ q → ∃ a b : I, minor2 (V p) (V q) a b ≠ 0

theorem projective_label_injective (V : PointLabel → I → K) (hV : AtlasIndependent V) :
    Function.Injective (fun p => pointClass (V p)) := by
  intro p q h
  by_contra hn
  obtain ⟨a,b,hab⟩ := hV p q hn
  obtain ⟨c,_,hc⟩ := Quotient.exact h
  exact not_proportional_of_minor2 hab ⟨c,hc.symm⟩

def projectivePoints (V : PointLabel → I → K) : Finset (PointClass K I) := by
  classical
  exact Finset.univ.image (fun p => pointClass (V p))

/-- The 66 labels count 66 actual projective classes, rather than merely
66 potentially coincident representatives. -/
theorem projectivePoints_card (V : PointLabel → I → K) (hV : AtlasIndependent V) :
    (projectivePoints V).card = 66 := by
  classical
  rw [projectivePoints,Finset.card_image_of_injective _ (projective_label_injective V hV)]
  simpa using point_card

private theorem onLine_swap {u v w : I → K} (h : OnLine u v w) : OnLine v u w := by
  obtain ⟨a,b,h⟩ := h
  exact ⟨b,a,by simpa [add_comm] using h⟩

private theorem onLine_permutation (v : Fin 3 → I → K) (hv : PairIndependent v)
    (h : OnLine (v 0) (v 1) (v 2)) (π : Equiv.Perm (Fin 3)) :
    OnLine (v (π 0)) (v (π 1)) (v (π 2)) := by
  obtain ⟨α,β,he⟩ := h
  have hα : α ≠ 0 := by
    intro hz
    obtain ⟨a,b,hab⟩ := hv 1 2 (by decide)
    exact not_proportional_of_minor2 hab ⟨β,by simpa [hz] using he⟩
  have hβ : β ≠ 0 := by
    intro hz
    obtain ⟨a,b,hab⟩ := hv 0 2 (by decide)
    exact not_proportional_of_minor2 hab ⟨α,by simpa [hz] using he⟩
  have h012 : OnLine (v 0) (v 1) (v 2) := ⟨α,β,he⟩
  have h021 : OnLine (v 0) (v 2) (v 1) := by
    refine ⟨-α/β,1/β,?_⟩
    funext x
    have hx := congrFun he x
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hx ⊢
    field_simp [hβ]
    linear_combination -hx
  have h120 : OnLine (v 1) (v 2) (v 0) := by
    refine ⟨-β/α,1/α,?_⟩
    funext x
    have hx := congrFun he x
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hx ⊢
    field_simp [hα]
    linear_combination -hx
  have all : ∀ i j k : Fin 3, i ≠ j → j ≠ k → i ≠ k → OnLine (v i) (v j) (v k) := by
    intro i j k hij hjk hik
    fin_cases i <;> fin_cases j <;> fin_cases k <;>
      first | exact (hij rfl).elim | exact (hjk rfl).elim | exact (hik rfl).elim |
        exact h012 | exact onLine_swap h012 | exact h021 | exact onLine_swap h021 |
        exact h120 | exact onLine_swap h120
  exact all _ _ _
    (fun h => (by decide : (0 : Fin 3) ≠ 1) (π.injective h))
    (fun h => (by decide : (1 : Fin 3) ≠ 2) (π.injective h))
    (fun h => (by decide : (0 : Fin 3) ≠ 2) (π.injective h))

theorem ordered_pencil_exists (V : PointLabel → I → K) (s : Fin 3 → K)
    (hV : AtlasIndependent V) (hs : Function.Injective s)
    (hline : ∀ r : RichLabel,
      OnLine (V (richPoints r 0)) (V (richPoints r 1)) (V (richPoints r 2)))
    (r : OrderedLabel) :
    ∃ P : Pencil K I, Nonconstant P ∧ Presents (fun j => V (orderedPoints r j)) s P ∧
      ∀ Q : Pencil K I, Presents (fun j => V (orderedPoints r j)) s Q → Equivalent P Q := by
  have hi : PairIndependent (fun j => V (richPoints r.1 j)) := by
    intro i j hij
    exact hV _ _ (fun he => hij (richPoints_distinct r.1 he))
  apply exists_unique_pencil
  · intro i j hij
    exact hi _ _ (fun he => hij (r.2.injective he))
  · exact hs
  · exact onLine_permutation _ hi (hline r.1) r.2

def chosenPencil (V : PointLabel → I → K) (s : Fin 3 → K)
    (hV : AtlasIndependent V) (hs : Function.Injective s)
    (hline : ∀ r : RichLabel,
      OnLine (V (richPoints r 0)) (V (richPoints r 1)) (V (richPoints r 2)))
    (r : OrderedLabel) : Pencil K I :=
  Classical.choose (ordered_pencil_exists V s hV hs hline r)

theorem chosenPencil_presents (V : PointLabel → I → K) (s : Fin 3 → K)
    (hV : AtlasIndependent V) (hs : Function.Injective s)
    (hline : ∀ r : RichLabel,
      OnLine (V (richPoints r 0)) (V (richPoints r 1)) (V (richPoints r 2)))
    (r : OrderedLabel) :
    Presents (fun j => V (orderedPoints r j)) s (chosenPencil V s hV hs hline r) :=
  (Classical.choose_spec (ordered_pencil_exists V s hV hs hline r)).2.1

theorem chosenPencil_class_injective (V : PointLabel → I → K) (s : Fin 3 → K)
    (hV : AtlasIndependent V) (hs : Function.Injective s)
    (hline : ∀ r : RichLabel,
      OnLine (V (richPoints r 0)) (V (richPoints r 1)) (V (richPoints r 2))) :
    Function.Injective (fun r => pencilClass (chosenPencil V s hV hs hline r)) := by
  intro r t he
  obtain ⟨c,_,hA,hB⟩ := Quotient.exact he
  have hr := chosenPencil_presents V s hV hs hline r
  have ht := chosenPencil_presents V s hV hs hline t
  apply orderedPoints_injective
  funext j
  by_contra hn
  obtain ⟨a,b,hab⟩ := hV _ _ hn
  obtain ⟨d,_,hd⟩ := hr j
  obtain ⟨e,he,hv⟩ := ht j
  have hh : e • V (orderedPoints t j) = (c*d) • V (orderedPoints r j) := by
    rw [←hv,←smul_smul,←hd]
    funext x
    simp only [Pencil.value,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,hA,hB]
    ring
  apply not_proportional_of_minor2 hab
  refine ⟨(c*d)/e,?_⟩
  funext x
  have hx := congrFun hh x
  simp only [Pi.smul_apply,smul_eq_mul] at hx ⊢
  field_simp [he]
  linear_combination -hx

def pencilClasses (V : PointLabel → I → K) (s : Fin 3 → K)
    (hV : AtlasIndependent V) (hs : Function.Injective s)
    (hline : ∀ r : RichLabel,
      OnLine (V (richPoints r 0)) (V (richPoints r 1)) (V (richPoints r 2))) :
    Finset (PencilClass K I) := by
  classical
  exact Finset.univ.image (fun r => pencilClass (chosenPencil V s hV hs hline r))

/-- Exactly 1212 actual pencils modulo one common scalar, with distinct
phase assignments and literal geometric points. -/
theorem pencilClasses_card (V : PointLabel → I → K) (s : Fin 3 → K)
    (hV : AtlasIndependent V) (hs : Function.Injective s)
    (hline : ∀ r : RichLabel,
      OnLine (V (richPoints r 0)) (V (richPoints r 1)) (V (richPoints r 2))) :
    (pencilClasses V s hV hs hline).card = 1212 := by
  classical
  rw [pencilClasses,Finset.card_image_of_injective _ (chosenPencil_class_injective V s hV hs hline)]
  simpa using ordered_card

end
end Paper2.Certificates.DihedralSupport.AtlasPencils

