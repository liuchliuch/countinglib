import ComplexCSP.Structure.MaltsevCSPWitness
import ComplexCSP.Complexity.CSPCode
namespace ComplexCSP.MaltsevWitness
open MaltsevRelations
variable {K : Type} {d s : ℕ} [DecidableEq K]
section Support
variable [Zero K]
def supportConstraints (L : Language (Fin d) K (Fin s)) (g : ComplexityCSPCode.Code)
    (hg : ComplexityCSPCode.Valid L g) : List (FiniteConstraint d g.vertices) :=
  g.constraints.attach.map fun c =>
    let symbol : Fin s := ⟨c.val.1, (hg c.val c.property).choose⟩
    { arity := L.arity symbol
      scope := ComplexityCSPCode.scope L g c.val (hg c.val c.property)
      accept := fun x => decide (L.value symbol x ≠ 0) }
theorem supportConstraints_preserved (L : Language (Fin d) K (Fin s))
    (m : Operation (Fin d)) (hL : ∀ i, Preserves m {x | L.value i x ≠ 0})
    (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g) :
    TablesPreserved m (supportConstraints L g hg) := by
  intro c hc
  obtain ⟨row, _, rfl⟩ := List.mem_map.mp hc
  simpa [supportConstraints] using hL ⟨row.val.1, (hg row.val row.property).choose⟩
end Support
section Domain
variable [CommMonoidWithZero K] [Nontrivial K] [NoZeroDivisors K]
omit [DecidableEq K] in
theorem raw_eval_ne_zero_iff (L : Language (Fin d) K (Fin s))
    (g : ComplexityCSPCode.Code) (x : Fin g.vertices → Fin d) :
    ComplexityCSPCode.eval L g x ≠ 0 ↔ ∀ c ∈ g.constraints,
      ComplexityCSPCode.entryValue L (ComplexityCSPCode.constraintEntry L g x c) ≠ 0 := by
  simp [ComplexityCSPCode.eval, ComplexityCSPCode.assignmentWord, List.prod_eq_zero_iff]
theorem supportConstraints_correct (L : Language (Fin d) K (Fin s))
    (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g) (x : Fin g.vertices → Fin d) :
    Satisfies (supportConstraints L g hg) x ↔ ComplexityCSPCode.eval L g x ≠ 0 := by
  rw [raw_eval_ne_zero_iff]
  simp only [Satisfies, supportConstraints, List.forall_mem_map]
  constructor
  · intro h c hc
    have ht := h ⟨c, hc⟩ (List.mem_attach _ _)
    simpa [ComplexityCSPCode.constraintEntry, hg c hc, ComplexityCSPCode.entryValue] using ht
  · intro h c _
    have ht := h c.val c.property
    simpa [ComplexityCSPCode.constraintEntry, hg c.val c.property, ComplexityCSPCode.entryValue] using ht
def rawSupportWitness (L : Language (Fin d) K (Fin s)) (m : Operation (Fin d)) (defaultValue : Fin d)
    (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g) : StoredCode d g.vertices :=
  construct m defaultValue (supportConstraints L g hg)
theorem rawSupportWitness_correct (L : Language (Fin d) K (Fin s)) {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hL : ∀ i, Preserves m {x | L.value i x ≠ 0}) (defaultValue : Fin d)
    (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g) :
    Correct (rawSupportWitness L m defaultValue g hg).toCode {x | ComplexityCSPCode.eval L g x ≠ 0} := by
  have h := construct_correct hm defaultValue (supportConstraints L g hg) (supportConstraints_preserved L m hL g hg)
  have he : {x | Satisfies (supportConstraints L g hg) x} = {x | ComplexityCSPCode.eval L g x ≠ 0} := by
    ext x
    exact supportConstraints_correct L g hg x
  rw [he] at h
  exact h
theorem rawSupportWitness_seed (L : Language (Fin d) K (Fin s)) {m : Operation (Fin d)} (hm : IsMaltsev m)
    (hL : ∀ i, Preserves m {x | L.value i x ≠ 0}) (defaultValue : Fin d)
    (g : ComplexityCSPCode.Code) (hg : ComplexityCSPCode.Valid L g) :
    (rawSupportWitness L m defaultValue g hg).seed.isSome = true ↔ ∃ x, ComplexityCSPCode.eval L g x ≠ 0 := by
  have h := construct_seed_correct hm defaultValue (supportConstraints L g hg) (supportConstraints_preserved L m hL g hg)
  simpa only [rawSupportWitness,supportConstraints_correct] using h
end Domain
end ComplexCSP.MaltsevWitness
