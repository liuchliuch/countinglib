import ComplexCSP.Complexity.CSPReplacement
import ComplexCSP.Algebra.WorkingField

/-! # An actual common number field for arbitrary algebraic table replacement -/
noncomputable section
open Classical
namespace ComplexCSP.ComplexityReplacementField
open PlanarHom PlanarHom.Complexity ComplexityCSPCode
variable {D : Type} [Fintype D] {s : ℕ} (L : Language D ℂ (Fin s))
variable (G : (i : Fin s) → (Fin (L.arity i) → D) → ℂ)

def paired : Language D ℂ (Fin s × Bool) where
  arity i := L.arity i.1
  arity_pos i := L.arity_pos i.1
  value i a := if i.2 then G i.1 a else L.value i.1 a

def field := (paired L G).workingField

theorem field_finiteDimensional
    (hL : ∀ i a,IsAlgebraic ℚ (L.value i a)) (hG : ∀ i a,IsAlgebraic ℚ (G i a)) :
    FiniteDimensional ℚ (field L G) := by
  apply (paired L G).workingField_finiteDimensional
  rintro ⟨i,b⟩ a
  cases b
  · exact hL i a
  · exact hG i a

def basis (hL : ∀ i a,IsAlgebraic ℚ (L.value i a)) (hG : ∀ i a,IsAlgebraic ℚ (G i a)) :
    Module.Basis (Fin (Module.finrank ℚ (field L G))) ℚ (field L G) := by
  letI := field_finiteDimensional L G hL hG
  exact Module.finBasis ℚ (field L G)

def sourceLanguage : Language D (field L G) (Fin s) where
  arity := L.arity
  arity_pos := L.arity_pos
  value i a := ⟨L.value i a,(paired L G).value_mem_workingField (i,false) a⟩

def targetValues (i : Fin s) (a : Fin ((sourceLanguage L G).arity i) → D) : field L G :=
  ⟨G i a,(paired L G).value_mem_workingField (i,true) a⟩

theorem compatible_of_embedding {I K : Type} [Field K] (σ : K →+* ℂ)
    (A B : I → K) (h : ProductCompatibility.Compatible (fun i => σ (A i)) (fun i => σ (B i))) :
    ProductCompatibility.Compatible A B := by
  intro xs ys hl hx hy he
  apply σ.injective
  simp only [map_list_prod,List.map_map,Function.comp_def]
  exact h xs ys hl (fun i hi => (map_ne_zero σ).mpr (hx i hi))
    (fun i hi => (map_ne_zero σ).mpr (hy i hi))
    (by simpa only [map_list_prod,List.map_map,Function.comp_def] using congrArg σ he)

/-- The actual shared finite-field encoding supplies the full machine reduction.
Product consistency is a finite algebraic condition, subsequently proved for
legal purification by its constructed multiplicative map. -/
def reduction
    (hL : ∀ i a,IsAlgebraic ℚ (L.value i a)) (hG : ∀ i a,IsAlgebraic ℚ (G i a))
    (hc : ProductCompatibility.Compatible (entryValue L) (ComplexityCSPReplacement.targetEntry L G))
    (hz : ∀ i a,L.value i a=0 → G i a=0) :
    PromisePolyTimeTuringReduction
      (ComplexityCSPCountReduction.partitionProblem
        (ComplexityCSPReplacement.language (sourceLanguage L G) (targetValues L G)) (basis L G hL hG))
      (ComplexityCSPCountReduction.partitionProblem (sourceLanguage L G) (basis L G hL hG)) := by
  let σ := (field L G).subtype
  let A := ComplexityCSPNodes.alphabet (sourceLanguage L G)
  let B := ComplexityCSPReplacement.targetAlphabet (sourceLanguage L G) (targetValues L G)
  let e : Fin (Fintype.card (Entry (sourceLanguage L G))) → Entry L :=
    (Fintype.equivFin (Entry (sourceLanguage L G))).symm
  have hA (i) : σ (A i)=entryValue L (e i) := by
    unfold σ A ComplexityCSPNodes.alphabet e
    cases (Fintype.equivFin (Entry (sourceLanguage L G))).symm i <;> rfl
  have hB (i) : σ (B i)=ComplexityCSPReplacement.targetEntry L G (e i) := by
    unfold σ B ComplexityCSPReplacement.targetAlphabet e
    cases (Fintype.equivFin (Entry (sourceLanguage L G))).symm i <;> rfl
  apply ComplexityCSPReplacement.reduction (sourceLanguage L G) (targetValues L G) (basis L G hL hG)
  · apply compatible_of_embedding σ A B
    convert hc.comp e using 1
    · exact funext hA
    · exact funext hB
  · intro i hi
    change A i=0 at hi
    apply σ.injective
    change σ (B i)=σ 0
    rw [hB,map_zero]
    have ha : entryValue L (e i)=0 := by rw [←hA,hi,map_zero]
    cases he : e i with
    | none => simp [he,entryValue] at ha
    | some ia => exact hz ia.1 ia.2 (by simpa [he,entryValue] using ha)

omit [Fintype D] in
theorem source_eval_coe (g : Code) (a : Fin g.vertices → D) :
    ((eval (sourceLanguage L G) g a : field L G) : ℂ)=eval L g a := by
  change (field L G).subtype _ = _
  simp only [eval,assignmentWord,map_list_prod,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro c hc
  simp only [constraintEntry]
  split_ifs <;> first | rfl | contradiction

theorem source_partition_coe (g : Code) :
    ((partition (sourceLanguage L G) g : field L G) : ℂ)=partition L g := by
  change (field L G).subtype _ = _
  simp only [partition,map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact source_eval_coe L G g a

omit [Fintype D] in
theorem target_eval_coe (g : Code) (a : Fin g.vertices → D) :
    ((eval (ComplexityCSPReplacement.language (sourceLanguage L G) (targetValues L G)) g a : field L G) : ℂ)=
      eval (ComplexityCSPReplacement.language L G) g a := by
  change (field L G).subtype _ = _
  simp only [eval,assignmentWord,map_list_prod,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro c hc
  simp only [constraintEntry]
  split_ifs <;> first | rfl | contradiction

theorem target_partition_coe (g : Code) :
    ((partition (ComplexityCSPReplacement.language (sourceLanguage L G) (targetValues L G)) g : field L G) : ℂ)=
      partition (ComplexityCSPReplacement.language L G) g := by
  change (field L G).subtype _ = _
  simp only [partition,map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact target_eval_coe L G g a

end ComplexCSP.ComplexityReplacementField
