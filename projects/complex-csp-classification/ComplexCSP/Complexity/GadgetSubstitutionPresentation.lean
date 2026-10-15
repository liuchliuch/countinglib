import ComplexCSP.Complexity.GadgetSubstitutionCode

set_option backward.isDefEq.respectTransparency false

/-! # Raw encoding of the literal finite gadget presentations -/
namespace ComplexCSP.ComplexityGadgetSubstitution
open ComplexityCSPCode
open scoped BigOperators

variable {D K : Type} {s b : ℕ} {L : Language D K (Fin s)}

def constraintCode {h : ℕ} (c : Constraint L (Fin b ⊕ Fin h)) : Gate :=
  (c.symbol.val, List.ofFn (fun i => (finSumFinEquiv (c.scope i)).val))

def presentationTemplate (P : Presentation L (Fin b)) : Template :=
  ⟨b, P.hidden, P.inst.constraints.map constraintCode⟩

def presentationCode (P : Presentation L (Fin b)) : Code := (presentationTemplate P).code

theorem constraintCode_valid {h : ℕ} (c : Constraint L (Fin b ⊕ Fin h)) :
    ConstraintValid L (b+h) (constraintCode c) := by
  refine ⟨c.symbol.isLt, ?_, ?_⟩
  · simp [constraintCode]
  · intro v hv
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
    exact (finSumFinEquiv (c.scope i)).isLt

theorem presentationCode_valid (P : Presentation L (Fin b)) : Valid L (presentationCode P) := by
  intro c hc
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hc
  exact constraintCode_valid a

/-- The decoded scope retains every original occurrence index. -/
theorem scope_constraintCode {h : ℕ} (c : Constraint L (Fin b ⊕ Fin h))
    (g : Code) (hg : ConstraintValid L g.vertices (constraintCode c))
    (i : Fin (L.arity c.symbol)) :
    (scope L g (constraintCode c) hg i).val = (finSumFinEquiv (c.scope i)).val := by
  simp [scope, constraintCode]

/-- Decoding the literal presentation code only applies the concrete bijection
from boundary/private variables to the complete finite variable set. -/
theorem toInstance_presentationCode (P : Presentation L (Fin b)) :
    toInstance L (presentationCode P) (presentationCode_valid P) =
      P.inst.mapVariables (fun v => Sum.inr (finSumFinEquiv v)) := by
  unfold toInstance presentationCode presentationTemplate Template.code Instance.mapVariables
  apply congrArg Instance.mk
  rw [List.attach_map, List.map_map]
  calc
    _ = P.inst.constraints.attach.map
        (fun c => c.val.rename (fun v => Sum.inr (finSumFinEquiv v))) := by
      apply List.map_congr_left
      intro c _
      apply congrArg (Constraint.mk c.val.symbol)
      funext i
      apply congrArg Sum.inr
      apply Fin.ext
      exact scope_constraintCode c.val _ _ i
    _ = _ := List.attach_map_val (l := P.inst.constraints)
      (f := fun c => c.rename (fun v => Sum.inr (finSumFinEquiv v)))

/-- Exact degree transport through the raw codec. -/
theorem degreeDivisible_presentationCode (P : Presentation L (Fin b)) (δ : ℕ)
    (hP : P.DegreeDivisible δ) :
    (toInstance L (presentationCode P) (presentationCode_valid P)).DegreeDivisible δ := by
  rw [toInstance_presentationCode]
  exact hP.mapVariables _

/-- Value of an encoded presentation for a fixed assignment of all its variables. -/
theorem eval_presentationCode [CommMonoid K] (P : Presentation L (Fin b))
    (σ : Fin (b+P.hidden) → D) :
    ComplexityCSPCode.eval L (presentationCode P) σ =
      P.inst.eval (fun i => σ (Fin.castAdd P.hidden i))
        (fun j => σ (Fin.natAdd b j)) := by
  rw [← eval_toInstance L (presentationCode P) (presentationCode_valid P),
    toInstance_presentationCode]
  simp only [ComplexCSP.Instance.eval, Instance.mapVariables, List.map_map, Function.comp_def,
    Constraint.eval_rename]
  congr 2
  funext c
  unfold Constraint.eval
  congr 1
  funext i
  simp only [Function.comp_apply]
  cases c.scope i <;> rfl

/-- Summing all code variables is the sum of the original pinned gadget table. -/
theorem partition_presentationCode [CommSemiring K] [Fintype D]
    (P : Presentation L (Fin b)) :
    ComplexityCSPCode.partition L (presentationCode P) = ∑ a : Fin b → D, P.table a := by
  unfold ComplexityCSPCode.partition
  simp only [eval_presentationCode]
  let e : ((Fin b → D) × (Fin P.hidden → D)) ≃ (Fin (b+P.hidden) → D) :=
    (Equiv.sumArrowEquivProdArrow (Fin b) (Fin P.hidden) D).symm.trans
      (finSumFinEquiv.arrowCongr (Equiv.refl D))
  let f := fun σ : Fin (b+P.hidden) → D =>
    P.inst.eval (fun i => σ (Fin.castAdd P.hidden i)) (fun j => σ (Fin.natAdd b j))
  have he (a : Fin b → D) (z : Fin P.hidden → D) : f (e (a,z)) = P.inst.eval a z := by
    dsimp [f,e]
    congr 1 <;> funext i <;> simp
  change (∑ σ, f σ) = _
  rw [← e.sum_comp f, Fintype.sum_prod_type]
  simp only [he, Presentation.table, Instance.partition]

private theorem remap_presentation_variable {r : ℕ}
    (P : Presentation L (Fin r)) (offset : ℕ) (f : Fin r → Fin b)
    (v : Fin r ⊕ Fin P.hidden) :
    remapVertex (presentationTemplate P) offset (List.ofFn (fun i => (f i).val))
        (finSumFinEquiv v).val =
      Sum.elim (fun i => (f i).val) (fun j => offset+j.val) v := by
  cases v with
  | inl i =>
    simp only [finSumFinEquiv_apply_left, Fin.coe_castAdd, Sum.elim_inl, remapVertex,
      presentationTemplate, i.isLt, if_true]
    rw [List.getD_eq_getElem _ _ (by simp)]
    simp
  | inr j =>
    simp [finSumFinEquiv_apply_right, remapVertex, presentationTemplate]

/-- The raw fresh-variable attachment is exactly the canonical finite-index
encoding of typed disjoint-copy gluing. -/
theorem presentationCode_mul_rename {r : ℕ}
    (Q : Presentation L (Fin b)) (P : Presentation L (Fin r)) (f : Fin r → Fin b) :
    presentationCode (Q.mul (P.rename f)) =
      attachTemplate (presentationTemplate P) (presentationCode Q)
        (List.ofFn (fun i => (f i).val)) := by
  unfold presentationCode presentationTemplate Template.code Presentation.mul Presentation.rename
  simp only [Instance.renameHidden, Instance.glue, Instance.renameBoundary, List.map_append,
    List.map_map, attachTemplate, Nat.add_assoc]
  congr 1
  apply congrArg₂ (· ++ ·)
  · apply List.map_congr_left
    intro c _
    unfold constraintCode Constraint.rename
    apply congrArg (Prod.mk c.symbol.val)
    apply congrArg List.ofFn
    funext i
    simp only [Function.comp_apply, Sum.map]
    cases c.scope i <;> simp
  · apply List.map_congr_left
    intro c _
    unfold constraintCode remapConstraint Constraint.rename
    apply congrArg (Prod.mk c.symbol.val)
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    have he := remap_presentation_variable P (b+Q.hidden) f (c.scope i)
    change _ = remapVertex (presentationTemplate P) (b+Q.hidden)
      (List.ofFn (fun i => (f i).val)) (finSumFinEquiv (c.scope i)).val
    rw [he]
    simp only [Function.comp_apply, Sum.map]
    cases c.scope i <;> simp [Nat.add_assoc]

end ComplexCSP.ComplexityGadgetSubstitution
