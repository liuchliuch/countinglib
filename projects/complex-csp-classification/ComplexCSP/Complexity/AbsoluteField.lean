import ComplexCSP.Complexity.CSPReplacement
import ComplexCSP.Algebra.WorkingField

/-! # Constructing the common exact field for an absolute-weight reduction

The language is fixed. Its original entries and their magnitudes supply genuine
finite algebraic generators; their field and basis are static program data.
-/
noncomputable section
open Classical
namespace ComplexCSP.ComplexityAbsoluteField
open scoped BigOperators
open ComplexityCSPCode PlanarHom PlanarHom.Complexity
variable {D : Type} [Fintype D] {s : ℕ} (L : Language D ℂ (Fin s))

theorem norm_algebraic {z : ℂ} (hz : IsAlgebraic ℚ z) :
    IsAlgebraic ℚ (‖z‖ : ℂ) := by
  have hc : IsIntegral ℚ (star z) :=
    IsIntegral.map (Complex.conjAe.restrictScalars ℚ) hz.isIntegral
  have hm := hz.isIntegral.mul hc
  have he : (‖z‖ : ℂ)^2 = z * star z := (Complex.mul_conj' z).symm
  apply IsIntegral.isAlgebraic
  apply IsIntegral.of_pow (n := 2) (by norm_num)
  rwa [he]

def enlarged : Language D ℂ (Fin s × Bool) where
  arity i := L.arity i.1
  arity_pos i := L.arity_pos i.1
  value i a := if i.2 then (‖L.value i.1 a‖ : ℂ) else L.value i.1 a

def field : IntermediateField ℚ ℂ := (enlarged L).workingField

omit [Fintype D] in
theorem enlarged_algebraic (hL : ∀ i a, IsAlgebraic ℚ (L.value i a)) :
    ∀ i a, IsAlgebraic ℚ ((enlarged L).value i a) := by
  rintro ⟨i,b⟩ a
  cases b
  · exact hL i a
  · exact norm_algebraic (hL i a)

theorem field_finiteDimensional (hL : ∀ i a, IsAlgebraic ℚ (L.value i a)) :
    FiniteDimensional ℚ (field L) :=
  (enlarged L).workingField_finiteDimensional (enlarged_algebraic L hL)

def basis (hL : ∀ i a, IsAlgebraic ℚ (L.value i a)) :
    Module.Basis (Fin (Module.finrank ℚ (field L))) ℚ (field L) := by
  letI := field_finiteDimensional L hL
  exact Module.finBasis ℚ (field L)

def sourceLanguage : Language D (field L) (Fin s) where
  arity := L.arity
  arity_pos := L.arity_pos
  value i a := ⟨L.value i a,(enlarged L).value_mem_workingField (i,false) a⟩

def absoluteValues (i : Fin s) (a : Fin ((sourceLanguage L).arity i) → D) : field L :=
  ⟨(‖L.value i a‖ : ℂ),(enlarged L).value_mem_workingField (i,true) a⟩

def absoluteLanguage : Language D ℂ (Fin s) :=
  ⟨L.arity,L.arity_pos,fun i a => (‖L.value i a‖ : ℂ)⟩

/-- No caller-supplied common field, basis or magnitude representation is needed. -/
def reduction (hL : ∀ i a, IsAlgebraic ℚ (L.value i a)) :
    PromisePolyTimeTuringReduction
      (ComplexityCSPCountReduction.partitionProblem
        (ComplexityCSPReplacement.language (sourceLanguage L) (absoluteValues L)) (basis L hL))
      (ComplexityCSPCountReduction.partitionProblem (sourceLanguage L) (basis L hL)) :=
  ComplexityCSPReplacement.absoluteReduction (sourceLanguage L) (absoluteValues L) (basis L hL)
    (field L).subtype (fun _ _ => rfl)

omit [Fintype D] in
theorem source_eval_coe (g : Code) (σ : Fin g.vertices → D) :
    ((eval (sourceLanguage L) g σ : field L) : ℂ) = eval L g σ := by
  change (field L).subtype _ = _
  simp only [eval,assignmentWord,map_list_prod,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro c hc
  simp only [constraintEntry]
  split_ifs <;> first | rfl | contradiction

theorem source_partition_coe (g : Code) :
    ((partition (sourceLanguage L) g : field L) : ℂ) = partition L g := by
  change (field L).subtype _ = _
  simp only [partition,map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact source_eval_coe L g a

omit [Fintype D] in
theorem absolute_eval_coe (g : Code) (σ : Fin g.vertices → D) :
    ((eval (ComplexityCSPReplacement.language (sourceLanguage L) (absoluteValues L)) g σ : field L) : ℂ) =
      eval (absoluteLanguage L) g σ := by
  change (field L).subtype _ = _
  simp only [eval,assignmentWord,map_list_prod,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro c hc
  simp only [constraintEntry]
  split_ifs <;> first | rfl | contradiction

theorem absolute_partition_coe (g : Code) :
    ((partition (ComplexityCSPReplacement.language (sourceLanguage L) (absoluteValues L)) g : field L) : ℂ) =
      partition (absoluteLanguage L) g := by
  change (field L).subtype _ = _
  simp only [partition,map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact absolute_eval_coe L g a

end ComplexCSP.ComplexityAbsoluteField
