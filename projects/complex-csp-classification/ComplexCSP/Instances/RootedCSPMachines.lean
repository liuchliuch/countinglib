import ComplexCSP.Instances.RootedCSPProjection
import ComplexCSP.Complexity.GadgetSubstitutionMachines
import ComplexCSP.Complexity.CSPCountReduction

/-! # Genuine finite-control root attachments and recovery arithmetic -/
namespace ComplexCSP.RootedCSPProjection
open PlanarHom PlanarHom.Complexity PairProjectionMachines
open ComplexityCSPCode ComplexityGadgetSubstitution
open scoped BigOperators

/-- A fixed finite query family is materialized by actual list constructors. -/
theorem fp_fixedList {A X Y : Type} (ex : BitEncoding X) (ey : BitEncoding Y)
    (xs : List A) (f : X → A → Y) (hf : ∀ a ∈ xs, FP ex ey (fun x => f x a)) :
    FP ex ey.list (fun x => xs.map (f x)) := by
  induction xs with
  | nil => exact fp_const _ _ []
  | cons a as ih =>
    exact ((hf a (by simp)).pair (ih (fun b hb => hf b (by simp [hb])))).comp
      (ListMutationMachines.fp_cons ey)

theorem fp_getD {Y : Type} (ey : BitEncoding Y) (v : ℕ) (d : Y) :
    FP ey.list ey (fun ys => ys.getD v d) := by
  induction v with
  | zero => exact (ListDecompositionMachines.fp_headD ey d).congr (fun xs => by cases xs <;> rfl)
  | succ v ih =>
    exact ((ListDecompositionMachines.fp_tail ey d).comp ih).congr (fun xs => by cases xs <;> rfl)

variable {D K : Type} {s : ℕ} {L : Language D K (Fin s)}

/-- Attach exactly one fixed rooted gadget at the first vertex. -/
def query (P : Presentation L (Fin 1)) (g : Code) : Code :=
  attachTemplate (presentationTemplate P) g [0]

theorem fp_query (P : Presentation L (Fin 1)) : FP encoding encoding (query P) :=
  ((fp_id encoding).pair (fp_const encoding BitEncoding.nat.list [0])).comp
    (fp_attachTemplate (presentationTemplate P))

theorem query_presentationCode (P Q : Presentation L (Fin 1)) :
    query P (presentationCode Q) = presentationCode (Q.mul (P.rename id)) := by
  rw [presentationCode_mul_rename]
  rfl

variable [Fintype D] [CommSemiring K]

theorem query_partition (P Q : Presentation L (Fin 1)) :
    partition L (query P (presentationCode Q)) = partition L (presentationCode (Q.mul P)) := by
  rw [query_presentationCode,partition_presentationCode,partition_presentationCode]
  simp only [Presentation.table_mul,Presentation.table_rename,Function.comp_id]

omit [Fintype D] [CommSemiring K] in
theorem query_valid (P Q : Presentation L (Fin 1)) : Valid L (query P (presentationCode Q)) := by
  rw [query_presentationCode]
  exact presentationCode_valid _

end ComplexCSP.RootedCSPProjection

namespace ComplexCSP.RootedCSPRecovery
open PlanarHom PlanarHom.Complexity PairProjectionMachines
open scoped BigOperators
variable {K : Type} [Field K] [Algebra ℚ K] {d n : ℕ}

/-- Exact recovery charges ordinary arithmetic in the fixed rational basis. -/
def recover (c : Fin n → K) (answers : List K) : K := ∑ j, c j * answers.getD j.val 0

private theorem fp_sum {X I : Type} (basis : Module.Basis (Fin d) ℚ K)
    (ex : BitEncoding X) (S : Finset I) (f : X → I → K)
    (hf : ∀ i ∈ S, FP ex (numberFieldEncoding basis) (fun x => f x i)) :
    FP ex (numberFieldEncoding basis) (fun x => ∑ i ∈ S, f x i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using fp_const ex (numberFieldEncoding basis) (0 : K)
  | @insert i S hi ih =>
    exact (((hf i (Finset.mem_insert_self _ _)).pair
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))).comp
        (FixedFieldArithmetic.fp_addition basis)).congr (fun x => by simp [hi])

theorem fp_recover (basis : Module.Basis (Fin d) ℚ K) (c : Fin n → K) :
    FP (numberFieldEncoding basis).list (numberFieldEncoding basis) (recover c) := by
  apply fp_sum basis _ Finset.univ
  intro i _
  exact ((fp_const _ (numberFieldEncoding basis) (c i)).pair
    (RootedCSPProjection.fp_getD (numberFieldEncoding basis) i.val 0)).comp
      (FixedFieldArithmetic.fp_multiplication basis)

omit [Algebra ℚ K] in
@[simp] theorem recover_ofFn (c v : Fin n → K) : recover c (List.ofFn v) = ∑ j, c j * v j := by
  simp [recover]

end ComplexCSP.RootedCSPRecovery
