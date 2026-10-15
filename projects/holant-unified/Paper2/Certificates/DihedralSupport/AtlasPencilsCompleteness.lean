import Paper2.Certificates.DihedralSupport.AtlasPencilsCardinality
import Mathlib.SetTheory.Cardinal.Finite

/-! Completeness of the projective-pencil enumeration. Admissibility is stated
directly for a pencil's three actual values. The independently checked atlas
geometry supplies exhaustivity of collinear triples; no enumeration or desired
cardinality is assumed as part of the pencil condition. -/
namespace Paper2.Certificates.DihedralSupport.AtlasPencils
open AtlasGeometry AtlasCounts
noncomputable section
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option synthInstance.maxSize 10000

variable {K : Type*} [Field K] {I : Type*}

/-- Every actual collinear triple of distinct atlas points is one rich triple. -/
def TripleExhaustive (V : PointLabel → I → K) : Prop :=
  ∀ p : Fin 3 → PointLabel, Function.Injective p →
    OnLine (V (p 0)) (V (p 1)) (V (p 2)) →
      ∃ r : RichLabel, Finset.univ.image p = richSet r

/-- A nonconstant pencil whose three phase values are nonzero multiples of
three distinct atlas representatives. -/
def Admissible (V : PointLabel → I → K) (s : Fin 3 → K) (P : Pencil K I) : Prop :=
  Nonconstant P ∧ ∃ p : Fin 3 → PointLabel,
    Function.Injective p ∧ Presents (fun j => V (p j)) s P

/-- The equivalent condition before explicitly recording that the three
projective labels differ. Distinctness follows from nonconstant coefficients
and distinct phase values. -/
def SourceAdmissible (V : PointLabel → I → K) (s : Fin 3 → K) (P : Pencil K I) : Prop :=
  Nonconstant P ∧ ∀ j : Fin 3, ∃ p : PointLabel, ∃ c : K,
    c ≠ 0 ∧ P.value (s j) = c • V p

theorem value_pairIndependent (P : Pencil K I) (s : Fin 3 → K)
    (hP : Nonconstant P) (hs : Function.Injective s) :
    PairIndependent (fun j => P.value (s j)) := by
  obtain ⟨a,b,hab⟩ := hP
  intro i j hij
  refine ⟨a,b,?_⟩
  have he : minor2 (P.value (s i)) (P.value (s j)) a b =
      (s i - s j) * minor2 P.A P.B a b := by
    simp only [minor2,Pencil.value,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he]
  exact mul_ne_zero (sub_ne_zero.mpr (fun h => hij (hs h))) hab

theorem presents_labels_injective (V : PointLabel → I → K) (p : Fin 3 → PointLabel)
    (s : Fin 3 → K) (P : Pencil K I) (hP : Nonconstant P)
    (hs : Function.Injective s) (hp : Presents (fun j => V (p j)) s P) :
    Function.Injective p := by
  intro i j he
  by_contra hij
  obtain ⟨a,b,hab⟩ := value_pairIndependent P s hP hs i j hij
  obtain ⟨c,_,hc⟩ := hp i
  obtain ⟨d,_,hd⟩ := hp j
  apply hab
  change minor2 (P.value (s i)) (P.value (s j)) a b = 0
  dsimp only at hc hd
  rw [hc,hd,he]
  simp only [minor2,Pi.smul_apply,smul_eq_mul]
  ring

theorem sourceAdmissible_iff_admissible (V : PointLabel → I → K) (s : Fin 3 → K)
    (hs : Function.Injective s) (P : Pencil K I) :
    SourceAdmissible V s P ↔ Admissible V s P := by
  classical
  constructor
  · rintro ⟨hP,hcards⟩
    let p : Fin 3 → PointLabel := fun j => Classical.choose (hcards j)
    have hp : Presents (fun j => V (p j)) s P :=
      fun j => Classical.choose_spec (hcards j)
    exact ⟨hP,p,presents_labels_injective V p s P hP hs hp,hp⟩
  · rintro ⟨hP,p,_,hp⟩
    exact ⟨hP,fun j => ⟨p j,hp j⟩⟩

/-- Actual affine-pencil values give collinear representatives, including all
nonzero scaling coefficients in the conclusion's construction. -/
theorem presents_onLine (v : Fin 3 → I → K) (s : Fin 3 → K) (P : Pencil K I)
    (hs : Function.Injective s) (hP : Presents v s P) :
    OnLine (v 0) (v 1) (v 2) := by
  obtain ⟨d₀,_,h₀⟩ := hP 0
  obtain ⟨d₁,_,h₁⟩ := hP 1
  obtain ⟨d₂,hd₂,h₂⟩ := hP 2
  have h10 : s 1 - s 0 ≠ 0 := sub_ne_zero.mpr
    (fun he => (by decide : (1 : Fin 3) ≠ 0) (hs he))
  have hden : (s 1 - s 0) * d₂ ≠ 0 := mul_ne_zero h10 hd₂
  have hrel : (s 1 - s 2) • (d₀ • v 0) + (s 2 - s 0) • (d₁ • v 1) =
      (s 1 - s 0) • (d₂ • v 2) := by
    rw [←h₀,←h₁,←h₂]
    funext x
    simp only [Pencil.value,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    ring
  refine ⟨((s 1 - s 2) * d₀) / ((s 1 - s 0) * d₂),
    ((s 2 - s 0) * d₁) / ((s 1 - s 0) * d₂),?_⟩
  funext x
  have hx := congrFun hrel x
  simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hx ⊢
  field_simp [hden]
  linear_combination hx

/-- An ordering of a rich set is literally its three-point ordering composed
with one permutation. This also retains the phase assignment. -/
theorem orderedLabel_of_richSet (p : Fin 3 → PointLabel) (hp : Function.Injective p)
    (r : RichLabel) (hset : Finset.univ.image p = richSet r) :
    ∃ o : OrderedLabel, o.1 = r ∧ orderedPoints o = p := by
  classical
  have hex : ∀ j : Fin 3, ∃ i : Fin 3, richPoints r i = p j := by
    intro j
    have hj : p j ∈ richSet r := by
      rw [←hset]
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp hj
    exact ⟨i,hi⟩
  let f : Fin 3 → Fin 3 := fun j => Classical.choose (hex j)
  have hf : ∀ j, richPoints r (f j) = p j := fun j => Classical.choose_spec (hex j)
  have hinj : Function.Injective f := by
    intro i j hij
    apply hp
    rw [←hf i,←hf j,hij]
  let π : Equiv.Perm (Fin 3) := Equiv.ofBijective f
    ⟨hinj,Finite.surjective_of_injective hinj⟩
  refine ⟨(r,π),rfl,?_⟩
  funext j
  exact hf j

theorem chosenPencil_nonconstant (V : PointLabel → I → K) (s : Fin 3 → K)
    (hV : AtlasIndependent V) (hs : Function.Injective s)
    (hline : ∀ r : RichLabel,
      OnLine (V (richPoints r 0)) (V (richPoints r 1)) (V (richPoints r 2)))
    (r : OrderedLabel) : Nonconstant (chosenPencil V s hV hs hline r) :=
  (Classical.choose_spec (ordered_pencil_exists V s hV hs hline r)).1

theorem chosenPencil_admissible (V : PointLabel → I → K) (s : Fin 3 → K)
    (hV : AtlasIndependent V) (hs : Function.Injective s)
    (hline : ∀ r : RichLabel,
      OnLine (V (richPoints r 0)) (V (richPoints r 1)) (V (richPoints r 2)))
    (r : OrderedLabel) : Admissible V s (chosenPencil V s hV hs hline r) := by
  refine ⟨chosenPencil_nonconstant V s hV hs hline r,orderedPoints r,?_,
    chosenPencil_presents V s hV hs hline r⟩
  intro i j hij
  exact r.2.injective (richPoints_distinct r.1 hij)

theorem admissible_of_equivalent {V : PointLabel → I → K} {s : Fin 3 → K}
    {P Q : Pencil K I} (h : Equivalent P Q) (hP : Admissible V s P) :
    Admissible V s Q := by
  obtain ⟨c,hc,hA,hB⟩ := h
  obtain ⟨⟨a,b,hab⟩,p,hp,hpres⟩ := hP
  refine ⟨⟨a,b,?_⟩,p,hp,?_⟩
  · have he : minor2 Q.A Q.B a b = c ^ 2 * minor2 P.A P.B a b := by
      simp only [hA,hB,minor2,Pi.smul_apply,smul_eq_mul]
      ring
    rw [he]
    exact mul_ne_zero (pow_ne_zero 2 hc) hab
  · intro j
    obtain ⟨d,hd,hj⟩ := hpres j
    refine ⟨c*d,mul_ne_zero hc hd,?_⟩
    have hv : Q.value (s j) = c • P.value (s j) := by
      funext x
      simp only [Pencil.value,hA,hB,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
      ring
    rw [hv,hj,smul_smul]

/-- Completeness for every admissible pencil, rather than only the constructed
finite image. -/
theorem admissible_iff_mem_pencilClasses (V : PointLabel → I → K) (s : Fin 3 → K)
    (hV : AtlasIndependent V) (hs : Function.Injective s)
    (hline : ∀ r : RichLabel,
      OnLine (V (richPoints r 0)) (V (richPoints r 1)) (V (richPoints r 2)))
    (hex : TripleExhaustive V) (P : Pencil K I) :
    Admissible V s P ↔ pencilClass P ∈ pencilClasses V s hV hs hline := by
  classical
  constructor
  · rintro ⟨_,p,hp,hpres⟩
    obtain ⟨r,hr⟩ := hex p hp (presents_onLine _ s P hs hpres)
    obtain ⟨o,_,ho⟩ := orderedLabel_of_richSet p hp r hr
    have hpresent : Presents (fun j => V (orderedPoints o j)) s P := by
      simpa only [ho] using hpres
    have he : Equivalent (chosenPencil V s hV hs hline o) P :=
      (Classical.choose_spec (ordered_pencil_exists V s hV hs hline o)).2.2 P hpresent
    exact Finset.mem_image.mpr ⟨o,Finset.mem_univ o,Quotient.sound he⟩
  · intro hm
    obtain ⟨o,_,he⟩ := Finset.mem_image.mp hm
    exact admissible_of_equivalent (Quotient.exact he)
      (chosenPencil_admissible V s hV hs hline o)

/-- The set of all admissible common-scale pencil classes. Its definition
does not use the selected enumeration or a cardinality. -/
def admissibleClasses (V : PointLabel → I → K) (s : Fin 3 → K) :
    Set (PencilClass K I) :=
  {q | ∃ P : Pencil K I, pencilClass P = q ∧ Admissible V s P}

theorem admissibleClasses_eq_pencilClasses (V : PointLabel → I → K) (s : Fin 3 → K)
    (hV : AtlasIndependent V) (hs : Function.Injective s)
    (hline : ∀ r : RichLabel,
      OnLine (V (richPoints r 0)) (V (richPoints r 1)) (V (richPoints r 2)))
    (hex : TripleExhaustive V) :
    admissibleClasses V s = (pencilClasses V s hV hs hline : Set (PencilClass K I)) := by
  classical
  ext q
  constructor
  · rintro ⟨P,rfl,hP⟩
    exact (admissible_iff_mem_pencilClasses V s hV hs hline hex P).mp hP
  · intro hq
    obtain ⟨o,_,ho⟩ := Finset.mem_image.mp hq
    exact ⟨chosenPencil V s hV hs hline o,ho,
      chosenPencil_admissible V s hV hs hline o⟩

/-- Exactly 1212 *all* admissible pencils up to common nonzero scale. -/
theorem admissibleClasses_card (V : PointLabel → I → K) (s : Fin 3 → K)
    (hV : AtlasIndependent V) (hs : Function.Injective s)
    (hline : ∀ r : RichLabel,
      OnLine (V (richPoints r 0)) (V (richPoints r 1)) (V (richPoints r 2)))
    (hex : TripleExhaustive V) : Nat.card (admissibleClasses V s) = 1212 := by
  classical
  have hmem : ∀ q, q ∈ pencilClasses V s hV hs hline ↔ q ∈ admissibleClasses V s := by
    intro q
    rw [admissibleClasses_eq_pencilClasses V s hV hs hline hex]
    rfl
  calc
    Nat.card (admissibleClasses V s) = (pencilClasses V s hV hs hline).card :=
      Nat.subtype_card (pencilClasses V s hV hs hline) hmem
    _ = 1212 := pencilClasses_card V s hV hs hline

end
end Paper2.Certificates.DihedralSupport.AtlasPencils

