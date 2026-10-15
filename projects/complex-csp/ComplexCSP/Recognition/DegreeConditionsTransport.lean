import ComplexCSP.Recognition.DegreeGenerated
import ComplexCSP.Instances.ValueTransport

/-! # Coefficient transport preserves literal degree certificates

Only coefficient values change. Every constraint scope and occurrence count is
preserved, including repeated indices and all hidden variables.
-/
namespace ComplexCSP
variable {D K R S ι B H : Type}

@[simp] theorem Language.mapValues_comp [CommSemiring K] [CommSemiring R] [CommSemiring S]
    (L : Language D K ι) (f : K →+* R) (g : R →+* S) :
    (L.mapValues f).mapValues g = L.mapValues (g.comp f) := rfl

namespace Instance
variable [CommSemiring K] [CommSemiring R] {L : Language D K ι}

@[simp] theorem occurrences_mapValues (I : Instance L B H) (f : K →+* R) :
    (I.mapValues f).occurrences = I.occurrences := by
  simp only [occurrences, mapValues, List.flatMap_map]
  rfl

@[simp] theorem occurrenceDegree_mapValues [DecidableEq B] [DecidableEq H]
    (I : Instance L B H) (f : K →+* R) (v : B ⊕ H) :
    (I.mapValues f).occurrenceDegree v = I.occurrenceDegree v := by
  simp only [occurrenceDegree, occurrences_mapValues]

@[simp] theorem degreeDivisible_mapValues_iff [DecidableEq B] [DecidableEq H]
    (I : Instance L B H) (f : K →+* R) (δ : ℕ) :
    (I.mapValues f).DegreeDivisible δ ↔ I.DegreeDivisible δ := by
  simp only [DegreeDivisible, occurrenceDegree_mapValues]

@[simp] theorem degreeDivisible_sourceValues_iff [DecidableEq B] [DecidableEq H]
    (f : K →+* R) (I : Instance (L.mapValues f) B H) (δ : ℕ) :
    (I.sourceValues f).DegreeDivisible δ ↔ I.DegreeDivisible δ := by
  rw [← degreeDivisible_mapValues_iff (I.sourceValues f) f δ, mapValues_sourceValues]
end Instance

namespace DegreeGenerated
variable [CommSemiring K] [CommSemiring R] [Fintype D] [DecidableEq B]
    {L : Language D K ι} {δ : ℕ}

/-- The actual degree-certified witness maps along every coefficient homomorphism. -/
theorem mapValues {G : (B → D) → K} (hG : DegreeGenerated L δ G) (f : K →+* R) :
    DegreeGenerated (L.mapValues f) δ (fun a => f (G a)) := by
  obtain ⟨P,hP,rfl⟩ := hG
  refine ⟨⟨P.hidden,P.inst.mapValues f⟩,
    (Instance.degreeDivisible_mapValues_iff P.inst f δ).mpr hP, ?_⟩
  funext a
  exact Instance.partition_mapValues P.inst f a

/-- Every degree-generated mapped table has a source template with the very same
occurrence degrees. No source tables or hidden-variable counts are lost. -/
theorem mapValues_iff (f : K →+* R) (G : (B → D) → R) :
    DegreeGenerated (L.mapValues f) δ G ↔
      ∃ F : (B → D) → K, DegreeGenerated L δ F ∧ ∀ a, f (F a) = G a := by
  constructor
  · rintro ⟨P,hP,rfl⟩
    refine ⟨(P.inst.sourceValues f).partition, ?_, ?_⟩
    · exact ⟨⟨P.hidden,P.inst.sourceValues f⟩,
        (Instance.degreeDivisible_sourceValues_iff f P.inst δ).mpr hP, rfl⟩
    · intro a
      exact Instance.partition_sourceValues f P.inst a
  · rintro ⟨F,hF,h⟩
    have hg := hF.mapValues f
    have he : (fun a => f (F a)) = G := funext h
    rwa [he] at hg
end DegreeGenerated
end ComplexCSP
