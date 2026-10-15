import ComplexCSP.Complexity.CSPCountReduction

/-! # Exact finite-color reindexing and charged identity-query reductions

Color labels do not occur in the raw CSP Code: only variable indices and fixed
signature labels occur there. A fixed color equivalence therefore preserves the
literal query word. Assignment sums and the charged oracle machine are proved
explicitly; no domain-relabeling oracle or free-answer convention is assumed.
-/
namespace ComplexCSP.ComplexityCSPColorRelabeling
open scoped BigOperators
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityCSPCode

variable {D E K : Type} {s : ℕ} (L : Language D K (Fin s)) (e : E ≃ D)

/-- New colors E interpreted as original colors D by the fixed bijection. -/
def reindex : Language E K (Fin s) where
  arity := L.arity
  arity_pos := L.arity_pos
  value i a := L.value i (e ∘ a)

/-- The more usual forward-bijection convention is an alias. -/
def relabelLanguage (e : D ≃ E) : Language E K (Fin s) := reindex L e.symm

theorem constraintValid_reindex (n : ℕ) (c : ℕ × List ℕ) :
    ConstraintValid (reindex L e) n c ↔ ConstraintValid L n c := Iff.rfl

theorem valid_reindex (g : Code) : Valid (reindex L e) g ↔ Valid L g := Iff.rfl

/-- Pointwise semantics on all raw Codes, including their explicit invalid-row
unit defaults. No validity hypothesis is required. -/
theorem eval_reindex [CommMonoid K] (g : Code) (σ : Fin g.vertices → E) :
    eval (reindex L e) g σ = eval L g (e ∘ σ) := by
  unfold eval assignmentWord
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro c _
  change entryValue (reindex L e) (constraintEntry (reindex L e) g σ c) =
    entryValue L (constraintEntry L g (e ∘ σ) c)
  by_cases hc : ConstraintValid L g.vertices c
  · have hc' : ConstraintValid (reindex L e) g.vertices c := hc
    simp only [constraintEntry,dif_pos hc,dif_pos hc',entryValue]
    rfl
  · have hc' : ¬ ConstraintValid (reindex L e) g.vertices c := hc
    simp only [constraintEntry,dif_neg hc,dif_neg hc',entryValue]

/-- The actual assignment equivalence proves exact partition equality. Repeated
scope positions, repeated constraints and isolated variables are unchanged. -/
theorem partition_reindex [Fintype D] [Fintype E] [CommSemiring K] (g : Code) :
    partition (reindex L e) g = partition L g := by
  unfold partition
  simp_rw [eval_reindex L e g]
  exact (Equiv.piCongrRight (fun _ : Fin g.vertices => e)).sum_comp (eval L g)

theorem partition_relabelLanguage [Fintype D] [Fintype E] [CommSemiring K]
    (e : D ≃ E) (g : Code) : partition (relabelLanguage L e) g = partition L g :=
  partition_reindex L e.symm g

section Field
variable [Fintype D] [Fintype E] [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- The same exact input/output words define equal promised partition problems. -/
theorem partitionProblem_reindex :
    ComplexityCSPCountReduction.partitionProblem (reindex L e) basis =
      ComplexityCSPCountReduction.partitionProblem L basis := by
  have he : partition (reindex L e) = partition L := funext (partition_reindex L e)
  unfold ComplexityCSPCountReduction.partitionProblem
  rw [he]
  rfl

/-- A real single identity-query reduction. Its query construction/recovery are
FP machines, and answer bits are charged by the actual fixed-alphabet field
output bound. Equality of semantic problems alone is not used as a free oracle
cost assumption. -/
noncomputable def reduction : PromisePolyTimeTuringReduction
    (ComplexityCSPCountReduction.partitionProblem (reindex L e) basis)
    (ComplexityCSPCountReduction.partitionProblem L basis) := by
  classical
  let prepare : Code → Bits × List Code := fun g => ([],[g])
  have hp : FP encoding (BitEncoding.bits.prod encoding.list) prepare := by
    have hq := ((fp_id encoding).pair (fp_const encoding encoding.list [])).comp
      (ListMutationMachines.fp_cons encoding)
    exact (fp_const encoding BitEncoding.bits []).pair hq
  let recover : Bits × List K → K := fun a => a.2.headD 0
  have hrecover : FP (BitEncoding.bits.prod (numberFieldEncoding basis).list)
      (numberFieldEncoding basis) recover :=
    (fp_snd _ _).comp (ListDecompositionMachines.fp_headD (numberFieldEncoding basis) 0)
  let source := ComplexityCSPCountReduction.partitionProblem L basis
  let target := ComplexityCSPCountReduction.partitionProblem (reindex L e) basis
  let view : ∀ raw,target.valid raw → Code := fun _ h => h.choose
  have hs : ∀ raw h, encoding.encode (view raw h)=raw := fun _ h => h.choose_spec.2
  let bound := Classical.choose (exists_partition_output_bound L basis)
  have hbound := Classical.choose_spec (exists_partition_output_bound L basis)
  refine nonadaptiveReduction encoding BitEncoding.bits encoding
    (numberFieldEncoding basis) (numberFieldEncoding basis) target source prepare
    (partition L) recover (Classical.choice hp) (Classical.choice hrecover)
    view hs ?_ ?_ ?_ bound ?_
  · intro raw h out hout
    have he : out = view raw h := List.mem_singleton.mp hout
    subst out
    exact ⟨_,h.choose_spec.1,rfl⟩
  · intro out _
    exact encodedFunction_encode encoding (numberFieldEncoding basis) (partition L) [] out
  · intro raw h
    change (numberFieldEncoding basis).encode (partition L (view raw h)) =
      encodedFunction encoding (numberFieldEncoding basis) (partition (reindex L e)) [] raw
    conv_rhs => rw [← hs raw h,encodedFunction_encode]
    rw [partition_reindex L e]
  · intro raw h
    obtain ⟨g,hg,rfl⟩ := h
    simpa only [source,ComplexityCSPCountReduction.partitionProblem,encodedFunction_encode] using hbound g

/-- The identical charged machine also reduces in the reverse direction,
transported through the proved equality of both promise and output functions. -/
noncomputable def reverseReduction : PromisePolyTimeTuringReduction
    (ComplexityCSPCountReduction.partitionProblem L basis)
    (ComplexityCSPCountReduction.partitionProblem (reindex L e) basis) := by
  simpa only [partitionProblem_reindex] using reduction L e basis

theorem reindex_reduces_original : Nonempty (PromisePolyTimeTuringReduction
    (ComplexityCSPCountReduction.partitionProblem (reindex L e) basis)
    (ComplexityCSPCountReduction.partitionProblem L basis)) := ⟨reduction L e basis⟩

theorem original_reduces_reindex : Nonempty (PromisePolyTimeTuringReduction
    (ComplexityCSPCountReduction.partitionProblem L basis)
    (ComplexityCSPCountReduction.partitionProblem (reindex L e) basis)) :=
  ⟨reverseReduction L e basis⟩

end Field
end ComplexCSP.ComplexityCSPColorRelabeling
