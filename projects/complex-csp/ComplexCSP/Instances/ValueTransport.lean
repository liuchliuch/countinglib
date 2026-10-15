import ComplexCSP.Algebra.WorkingField
import ComplexCSP.Instances.PresentationAlgorithms

/-! # Exact coefficient-field transport

Literal constraint presentations are transported along coefficient ring maps.
This proves the semantics of working inside the one input number field; it does
not pretend to construct an executable field representation from encoded inputs.
-/
namespace ComplexCSP

variable {D K R ι B H : Type}

namespace Language

def mapValues [CommSemiring K] [CommSemiring R] (L : Language D K ι)
    (f : K →+* R) : Language D R ι where
  arity := L.arity
  arity_pos := L.arity_pos
  value i a := f (L.value i a)

end Language

namespace Instance
variable [CommSemiring K] [CommSemiring R] {L : Language D K ι}

def mapValues (I : Instance L B H) (f : K →+* R) : Instance (L.mapValues f) B H :=
  ⟨I.constraints.map (fun c => ⟨c.symbol,c.scope⟩)⟩

theorem eval_mapValues (I : Instance L B H) (f : K →+* R) (a : B → D) (b : H → D) :
    (I.mapValues f).eval a b = f (I.eval a b) := by
  unfold eval mapValues
  simp only [List.map_map, map_list_prod, List.map_map]
  rfl

theorem partition_mapValues [Fintype D] [Fintype H] [DecidableEq H]
    (I : Instance L B H) (f : K →+* R) (a : B → D) :
    (I.mapValues f).partition a = f (I.partition a) := by
  simp only [partition, eval_mapValues, map_sum]

/-- Actual generated presentations, including all hidden summations, commute
with coefficient homomorphisms. -/
theorem generated_mapValues [Fintype D] {G : (B → D) → K}
    (hG : Generated L G) (f : K →+* R) :
    Generated (L.mapValues f) (fun a => f (G a)) := by
  obtain ⟨n,I,hI⟩ := hG
  exact ⟨n,I.mapValues f,fun a => by rw [partition_mapValues,hI]⟩

/-- Reuse the same symbol/scope list in the source coefficient field. -/
def sourceValues (f : K →+* R) (I : Instance (L.mapValues f) B H) : Instance L B H :=
  ⟨I.constraints.map (fun c => ⟨c.symbol,c.scope⟩)⟩

@[simp] theorem mapValues_sourceValues (f : K →+* R) (I : Instance (L.mapValues f) B H) :
    (I.sourceValues f).mapValues f = I := by
  cases I with
  | mk cs =>
    simp only [mapValues,sourceValues,List.map_map]
    change Instance.mk (cs.map id) = Instance.mk cs
    rw [List.map_id]

@[simp] theorem partition_sourceValues [Fintype D] [Fintype H] [DecidableEq H]
    (f : K →+* R) (I : Instance (L.mapValues f) B H) (a : B → D) :
    f ((I.sourceValues f).partition a) = I.partition a := by
  rw [← partition_mapValues,mapValues_sourceValues]

/-- No generated tables are lost by coefficient interpretation: every mapped
instance has a literal source template with exactly the same finite scopes. -/
theorem generated_mapValues_iff [Fintype D] (f : K →+* R)
    (G : (B → D) → R) :
    Generated (L.mapValues f) G ↔
      ∃ F : (B → D) → K, Generated L F ∧ ∀ a, f (F a) = G a := by
  constructor
  · rintro ⟨n,I,hI⟩
    refine ⟨(I.sourceValues f).partition,⟨n,I.sourceValues f,fun _ => rfl⟩,?_⟩
    intro a
    rw [partition_sourceValues,hI]
  · rintro ⟨F,hF,h⟩
    have hg := generated_mapValues hF f
    have he : (fun a => f (F a)) = G := funext h
    rwa [he] at hg

end Instance

namespace Instance
variable {L : Language D ℂ ι}

/-- Every literal input symbol can be interpreted inside its actual input field. -/
noncomputable def inWorkingField (I : Instance L B H) : Instance L.workingFieldLanguage B H :=
  ⟨I.constraints.map (fun c => ⟨c.symbol,c.scope⟩)⟩

@[simp] theorem eval_inWorkingField (I : Instance L B H) (a : B → D) (b : H → D) :
    ((I.inWorkingField.eval a b : L.workingField) : ℂ) = I.eval a b := by
  change L.workingField.subtype
    ((I.inWorkingField.constraints.map (fun c => c.eval (Sum.elim a b))).prod) = I.eval a b
  rw [map_list_prod]
  simp only [inWorkingField, List.map_map, eval]
  rfl

@[simp] theorem partition_inWorkingField [Fintype D] [Fintype H] [DecidableEq H]
    (I : Instance L B H) (a : B → D) :
    ((I.inWorkingField.partition a : L.workingField) : ℂ) = I.partition a := by
  change L.workingField.subtype (∑ b : H → D, I.inWorkingField.eval a b) =
    ∑ b : H → D, I.eval a b
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro b hb
  exact eval_inWorkingField I a b

/-- The field-valued generated witness is constructed by changing only its
coefficient interpretation. Its complex interpretation is exactly the old table. -/
theorem generated_inWorkingField [Fintype D] {G : (B → D) → ℂ}
    (hG : Generated L G) :
    ∃ F : (B → D) → L.workingField,
      Generated L.workingFieldLanguage F ∧ ∀ a, (F a : ℂ) = G a := by
  obtain ⟨n,I,hI⟩ := hG
  refine ⟨I.inWorkingField.partition, ⟨n,I.inWorkingField,fun _ => rfl⟩, ?_⟩
  intro a
  rw [partition_inWorkingField,hI]

end Instance
end ComplexCSP
