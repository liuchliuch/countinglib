import Paper2.DegreeCSP.BooleanMaltsevRepair
import Paper2.DegreeCSP.BooleanSupportFromBO
import Paper2.DegreeCSP.BooleanSupportFromBOProjection
import Paper2.DegreeCSP.BooleanGeneratedSupport

/-! The finite relational repair is instantiated by actual degree-generated
tables. Every equality-free conjunction is a real product of presentations,
and its existential projection uses cancellation-safe genuine powers before
each Boolean summation. No common operation is assumed. -/
namespace Paper2.DegreeCSP.BooleanGeneratedMaltsev
open scoped BigOperators
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
attribute [local instance] Classical.propDecidable


def supports (F : SignatureFamily AlgebraicComplex) (k : ℕ) : Set (BooleanMaltsevRepair.Relation Bool) :=
  {R | ∃ f : Signature AlgebraicComplex R.arity,
    Generated F k f ∧ R.tuples = {x | f x ≠ 0}}

section Projection
variable {V : Type} [Fintype V]

abbrev Hidden (s : Finset V) (c : V) := {v : V // v ∉ s ∧ v ≠ c}

def scope (s : Finset V) (c : V) : V →
    Fin ((Fintype.card s + 1) + Fintype.card (Hidden s c)) := fun v =>
  if hs : v ∈ s then
    ((Fintype.equivFin s ⟨v,hs⟩).castSucc).castAdd _
  else if hc : v = c then
    (Fin.last (Fintype.card s)).castAdd _
  else Fin.natAdd (Fintype.card s + 1) (Fintype.equivFin (Hidden s c) ⟨v,hs,hc⟩)

def assignment (s : Finset V) (c : V) (x : V → Bool) (z : Bool)
    (y : Fin (Fintype.card (Hidden s c)) → Bool) : V → Bool := fun v =>
  if hs : v ∈ s then x v
  else if hc : v = c then z
  else y (Fintype.equivFin (Hidden s c) ⟨v,hs,hc⟩)

def row (s : Finset V) (x : V → Bool) : Fin (Fintype.card s) → Bool :=
  fun j => x ((Fintype.equivFin s).symm j)

theorem scope_value (s : Finset V) (c : V) (x : V → Bool) (z : Bool)
    (y : Fin (Fintype.card (Hidden s c)) → Bool) (v : V) :
    Fin.append (Fin.snoc (row s x) z) y (scope s c v) = assignment s c x z y v := by
  by_cases hs : v ∈ s
  · simp [scope,assignment,hs,row]
  · by_cases hc : v=c
    · subst v
      simp [scope,assignment,hs]
    · simp [scope,assignment,hs,hc]

theorem assignment_row (s : Finset V) (c : V) (x : V → Bool) (z : Bool)
    (y : Fin (Fintype.card (Hidden s c)) → Bool) (v : V) (hv : v ∈ s) :
    assignment s c x z y v = x v := by simp [assignment,hv]

theorem assignment_last (s : Finset V) (c : V) (hc : c ∉ s)
    (x : V → Bool) (z : Bool) (y : Fin (Fintype.card (Hidden s c)) → Bool) :
    assignment s c x z y c = z := by simp [assignment,hc]

theorem assignment_recover (s : Finset V) (c : V) (p : V → Bool) :
    assignment s c p (p c)
      (fun j => p ((Fintype.equivFin (Hidden s c)).symm j)) = p := by
  funext v
  by_cases hs : v ∈ s
  · simp [assignment,hs]
  · by_cases hc : v=c
    · simp [assignment,hc]
    · simp [assignment,hs,hc]

end Projection

theorem equalityfree_rectangularity (F : SignatureFamily AlgebraicComplex) (k : ℕ)
    (hBO : OriginalBO.AllGeneratedOriginalBO F k) :
    BooleanMaltsevRepair.EqualityFreeSingletonRectangularity (supports F k) := by
  classical
  intro V A _ _ C hC s c hc x y a b hxa hya hxb
  have hG : ∀ i, ∃ f : Signature AlgebraicComplex (C.relation i).arity,
      Generated F k f ∧ (C.relation i).tuples = {x | f x ≠ 0} := hC
  choose f hf hsupp using hG
  let aC : A → ℕ := fun i => (C.relation i).arity
  let denseScope : (i : A) → Fin (aC i) →
      Fin ((Fintype.card s + 1) + Fintype.card (Hidden s c)) :=
    fun i j => scope s c (C.scope i j)
  let dense : Signature AlgebraicComplex
      ((Fintype.card s + 1) + Fintype.card (Hidden s c)) :=
    fun w => ∏ i, f i (fun j => w (denseScope i j))
  have hdense : Generated F k dense := BooleanSupportFromBO.generated_conjunction aC f hf denseScope
  obtain ⟨g,hg,hgs⟩ := BooleanSupportFromBO.generated_exists_suffix hdense
  have hsupport (r : V → Bool) (z : Bool) :
      g (Fin.snoc (row s r) z) ≠ 0 ↔
        BooleanMaltsevRepair.ProjectLast {p | C.Satisfies p} s c r z := by
    rw [hgs]
    have he (w : Fin (Fintype.card (Hidden s c)) → Bool) :
        dense (Fin.append (Fin.snoc (row s r) z) w) ≠ 0 ↔
          C.Satisfies (assignment s c r z w) := by
      simp only [dense]
      rw [BooleanSupportFromBO.conjunction_support]
      simp only [BooleanMaltsevRepair.EqualityFreeConjunction.Satisfies,hsupp,Set.mem_ofPred_eq]
      apply forall_congr'
      intro i
      have hword : (fun j => Fin.append (Fin.snoc (row s r) z) w (denseScope i j)) =
          (fun j => assignment s c r z w (C.scope i j)) :=
        funext (fun j => scope_value s c r z w (C.scope i j))
      rw [hword]
    simp_rw [he]
    constructor
    · rintro ⟨w,hw⟩
      exact ⟨assignment s c r z w,hw,
        fun v hv => assignment_row s c r z w v hv,
        assignment_last s c hc r z w⟩
    · rintro ⟨p,hp,hr,hz⟩
      refine ⟨fun j => p ((Fintype.equivFin (Hidden s c)).symm j), ?_⟩
      have equal : assignment s c r z
          (fun j => p ((Fintype.equivFin (Hidden s c)).symm j)) = p := by
        funext v
        by_cases hv : v ∈ s
        · simp [assignment,hv,hr v hv]
        · by_cases hvc : v=c
          · subst v
            simp [assignment,hc,hz]
          · simp [assignment,hv,hvc]
      rwa [equal]
  have rect := BooleanSupportFromBO.rows_rectangular hBO hg
  apply (hsupport y b).mp
  exact rect (row s x) (row s y) a b
    ((hsupport x a).mpr hxa) ((hsupport y a).mpr hya) ((hsupport x b).mpr hxb)

theorem common_support_operation (F : SignatureFamily AlgebraicComplex) (k : ℕ)
    (hBO : OriginalBO.AllGeneratedOriginalBO F k) :
    ∃ m : BooleanStructure.Operation, BooleanStructure.IsMaltsev m ∧
      BooleanGeneratedSupport.CommonSupportOperation F k m := by
  obtain ⟨m,hm,hpres⟩ := BooleanMaltsevRepair.common_maltsev_of_equalityfree_rectangularity
    (supports F k) (equalityfree_rectangularity F k hBO)
  refine ⟨m,hm,?_⟩
  intro n f hf
  have hR : (⟨n,{x | f x ≠ 0}⟩ : BooleanMaltsevRepair.Relation Bool) ∈ supports F k := ⟨f,hf,rfl⟩
  exact hpres _ hR

end
end Paper2.DegreeCSP.BooleanGeneratedMaltsev
