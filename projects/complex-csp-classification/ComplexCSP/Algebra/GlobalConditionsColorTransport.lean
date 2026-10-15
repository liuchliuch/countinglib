import ComplexCSP.Structure.BlockOrthogonalityColorTransport
import ComplexCSP.Complexity.CSPColorRelabeling
import ComplexCSP.Recognition.DegreeConditions
import ComplexCSP.Instances.ValueTransport

/-! # Ordinary and degree joint BO under arbitrary finite color equivalence

Every generated presentation is transported with identical finite scopes and
hidden-variable count. The exact legal singleton purification is compared by
ambient invariance, and joint BO follows from its proved singleton equivalence.
No nonempty-domain assumption is used.
-/
set_option maxHeartbeats 1500000
noncomputable section
open Classical
namespace ComplexCSP.GlobalConditionsColorTransport
open scoped BigOperators
open ComplexityCSPColorRelabeling BlockOrthogonalityColorTransport
variable {D E K B H : Type} [Fintype D] [Fintype E] {s : ℕ}
variable (L : Language D K (Fin s)) (e : E ≃ D)

def sourceInstance (I : Instance (reindex L e) B H) : Instance L B H :=
  ⟨I.constraints.map (fun c => ⟨c.symbol,c.scope⟩)⟩

omit [Fintype D] [Fintype E] in
theorem eval_sourceInstance [CommMonoid K] (I : Instance (reindex L e) B H) (a : B → D) (b : H → D) :
    (sourceInstance L e I).eval a b=I.eval (e.symm ∘ a) (e.symm ∘ b) := by
  simp only [sourceInstance,Instance.eval,List.map_map,Constraint.eval,reindex]
  apply congrArg List.prod
  apply List.map_congr_left
  intro c hc
  change L.value c.symbol (fun i => Sum.elim a b (c.scope i))=
    L.value c.symbol (fun i => e (Sum.elim (e.symm ∘ a) (e.symm ∘ b) (c.scope i)))
  apply congrArg (L.value c.symbol)
  funext i
  cases hs : c.scope i <;> simp [Function.comp_def]

theorem partition_sourceInstance [CommSemiring K] [Fintype H] [DecidableEq H] (I : Instance (reindex L e) B H)
    (a : B → D) : (sourceInstance L e I).partition a=I.partition (e.symm ∘ a) := by
  simp only [Instance.partition,eval_sourceInstance]
  exact (Equiv.piCongrRight (fun _ : H => e.symm)).sum_comp (I.eval (e.symm ∘ a))

omit [Fintype D] [Fintype E] in
theorem occurrences_sourceInstance (I : Instance (reindex L e) B H) :
    (sourceInstance L e I).occurrences=I.occurrences := by
  simp only [sourceInstance,Instance.occurrences,List.flatMap_map]
  rfl

omit [Fintype D] [Fintype E] in
theorem degree_sourceInstance [DecidableEq B] [DecidableEq H]
    (I : Instance (reindex L e) B H) {δ : ℕ} (h : I.DegreeDivisible δ) :
    (sourceInstance L e I).DegreeDivisible δ := by
  intro v
  simpa only [Instance.occurrenceDegree,occurrences_sourceInstance] using h v

theorem generated_source [CommSemiring K] {F : (B → E) → K}
    (h : Instance.Generated (reindex L e) F) :
    Instance.Generated L (fun a => F (e.symm ∘ a)) := by
  obtain ⟨n,I,hI⟩ := h
  exact ⟨n,sourceInstance L e I,fun a => (partition_sourceInstance L e I a).trans (hI _)⟩

theorem degreeGenerated_source [CommSemiring K] [DecidableEq B] {δ : ℕ} {F : (B → E) → K}
    (h : DegreeGenerated (reindex L e) δ F) :
    DegreeGenerated L δ (fun a => F (e.symm ∘ a)) := by
  obtain ⟨P,hP,hF⟩ := h
  refine ⟨⟨P.hidden,sourceInstance L e P.inst⟩,degree_sourceInstance L e P.inst hP,?_⟩
  funext a
  exact (partition_sourceInstance L e P.inst a).trans (congrFun hF _)

omit [Fintype D] [Fintype E] in
theorem reindex_inverse : reindex (reindex L e) e.symm=L := by
  cases L with
  | mk ar hp v =>
    unfold reindex
    congr 1
    funext i a
    simp [Function.comp_def]

omit [Fintype D] [Fintype E] in
theorem reindex_mapValues [CommSemiring K] {R : Type} [CommSemiring R] (φ : K →+* R) :
    (reindex L e).mapValues φ=reindex (L.mapValues φ) e := rfl

section Complex
variable (A : Language D ℂ (Fin s))

/-- Forward invariance of the literal jointly purified family. -/
theorem jointBO_reindex (h : JointBO A) : JointBO (reindex A e) := by
  apply (jointBO_iff_singletonBO _).mpr
  intro T hT hpos
  have hgen := generated_source A e hT
  have hb := (jointBO_iff_singletonBO A).mp h (tableReindex T e.symm) hgen hpos
  have ht := singleton_reindex (tableReindex T e.symm) e hb
  have he : tableReindex (tableReindex T e.symm) e=T := tableReindex_inverse T e.symm
  rwa [he] at ht

/-- Forward invariance retains the actual occurrence-degree certificates. -/
theorem degreeJointBO_reindex (δ : ℕ) (h : DegreeJointBO A δ) : DegreeJointBO (reindex A e) δ := by
  apply (degreeJointBO_iff_singletonBO _ δ).mpr
  intro T hT hpos
  have hgen := degreeGenerated_source A e hT
  have hb := (degreeJointBO_iff_singletonBO A δ).mp h (tableReindex T e.symm) hgen hpos
  have ht := singleton_reindex (tableReindex T e.symm) e hb
  have he : tableReindex (tableReindex T e.symm) e=T := tableReindex_inverse T e.symm
  rwa [he] at ht

theorem jointBO_reindex_iff : JointBO (reindex A e) ↔ JointBO A := by
  constructor
  · intro h
    have hh := jointBO_reindex e.symm (reindex A e) h
    rwa [reindex_inverse A e] at hh
  · exact jointBO_reindex e A

theorem degreeJointBO_reindex_iff (δ : ℕ) : DegreeJointBO (reindex A e) δ ↔ DegreeJointBO A δ := by
  constructor
  · intro h
    have hh := degreeJointBO_reindex e.symm (reindex A e) δ h
    rwa [reindex_inverse A e] at hh
  · exact degreeJointBO_reindex e A δ

end Complex
end ComplexCSP.GlobalConditionsColorTransport
