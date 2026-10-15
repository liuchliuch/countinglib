import Paper2.DegreeCSP.GeneratedRestrictions

/-! Exact coordinate marginals of actual degree-generated presentations.
A bijective projection of the live support gives exactly one nonzero summand
per retained assignment, so the genuine hidden-variable sum loses no scalar or
coefficient. -/
namespace Paper2.DegreeCSP.GeneratedCoordinateMarginal
open scoped BigOperators
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local instance] Classical.propDecidable

variable {n r : ℕ}

abbrev Live (f : Signature AlgebraicComplex n) := {x : Fin n→Bool // f x≠0}
def liveProjection (f : Signature AlgebraicComplex n) (q : Fin r→Fin n) :
    Live f → (Fin r→Bool) := fun x j=>x.val (q j)

abbrev Complement (q : Fin r→Fin n) := {i : Fin n // i ∉ Set.range q}

def scopeAddress (q : Fin r→Fin n) (i : Fin n) :
    Fin (r+Fintype.card (Complement q)) :=
  if hi : i ∈ Set.range q then (Classical.choose hi).castAdd _
  else Fin.natAdd r (Fintype.equivFin (Complement q) ⟨i,hi⟩)

def assignment (q : Fin r→Fin n) (a : Fin r→Bool)
    (b : Fin (Fintype.card (Complement q))→Bool) (i : Fin n) : Bool :=
  if hi : i ∈ Set.range q then a (Classical.choose hi)
  else b (Fintype.equivFin (Complement q) ⟨i,hi⟩)

def hiddenAssignment (q : Fin r→Fin n) (x : Fin n→Bool) :
    Fin (Fintype.card (Complement q))→Bool :=
  fun i=>x ((Fintype.equivFin (Complement q)).symm i).val

theorem scope_assignment (q : Fin r→Fin n) (a : Fin r→Bool)
    (b : Fin (Fintype.card (Complement q))→Bool) :
    (fun i=>Fin.append a b (scopeAddress q i))=assignment q a b := by
  funext i
  unfold scopeAddress assignment
  split_ifs <;> simp

theorem assignment_selected (q : Fin r→Fin n) (hq : Function.Injective q)
    (a : Fin r→Bool) (b : Fin (Fintype.card (Complement q))→Bool) (j : Fin r) :
    assignment q a b (q j)=a j := by
  have hj : q j ∈ Set.range q := ⟨j,rfl⟩
  simp only [assignment,dite_eq_left hj]
  exact congrArg a (hq (Classical.choose_spec hj))

theorem assignment_complement (q : Fin r→Fin n) (a : Fin r→Bool)
    (b : Fin (Fintype.card (Complement q))→Bool) (i : Complement q) :
    assignment q a b i.val=b (Fintype.equivFin (Complement q) i) := by
  simp only [assignment,dite_eq_right i.property]

theorem assignment_recover (q : Fin r→Fin n) (x : Fin n→Bool) :
    assignment q (fun j=>x (q j)) (hiddenAssignment q x)=x := by
  funext i
  unfold assignment
  split_ifs with hi
  · exact congrArg x (Classical.choose_spec hi)
  · simp only [hiddenAssignment,Equiv.symm_apply_apply]

theorem assignment_hidden_injective (q : Fin r→Fin n) (a : Fin r→Bool) :
    Function.Injective (assignment q a) := by
  intro b d h
  funext i
  have he := congrFun h ((Fintype.equivFin (Complement q)).symm i).val
  simpa only [assignment_complement,Equiv.apply_symm_apply] using he

/-- The literal marginal sums the complement assignments of the original table. -/
def marginal (f : Signature AlgebraicComplex n) (q : Fin r→Fin n) :
    Signature AlgebraicComplex r := fun a=>
  ∑ b : Fin (Fintype.card (Complement q))→Bool,f (assignment q a b)

/-- Actual boundary pullback followed by the genuine finite suffix sum. -/
theorem generated_marginal {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (f : Signature AlgebraicComplex n) (hf : Generated F k f) (q : Fin r→Fin n) :
    Generated F k (marginal f q) := by
  have h := generated_sum_suffix (generated_pullback hf (scopeAddress q))
  convert h using 1
  funext a
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  exact (scope_assignment q a b).symm

/-- Live projection injectivity excludes every other nonzero summand. -/
theorem marginal_at_live (f : Signature AlgebraicComplex n) (q : Fin r→Fin n)
    (hq : Function.Injective q) (hp : Function.Injective (liveProjection f q))
    (x : Fin n→Bool) (hx : f x≠0) : marginal f q (fun j=>x (q j))=f x := by
  unfold marginal
  calc
    _ = f (assignment q (fun j=>x (q j)) (hiddenAssignment q x)) := by
      apply Finset.sum_eq_single (hiddenAssignment q x)
      · intro b _ hb
        by_contra hn
        have he : assignment q (fun j=>x (q j)) b=x := by
          apply congrArg Subtype.val (hp (a₁ := ⟨assignment q (fun j=>x (q j)) b,hn⟩)
            (a₂ := ⟨x,hx⟩) ?_)
          funext j
          change assignment q (fun j=>x (q j)) b (q j)=x (q j)
          exact assignment_selected q hq _ b j
        have hb0 : b=hiddenAssignment q x := assignment_hidden_injective q _
          (he.trans (assignment_recover q x).symm)
        exact hb hb0
      · intro hn
        exact False.elim (hn (Finset.mem_univ _))
    _ = f x := congrArg f (assignment_recover q x)

/-- A bijective live projection gives a full-support generated coordinate
marginal with the exact original coefficients on every live source word. -/
theorem generated_coordinate_marginal {F : SignatureFamily AlgebraicComplex} {k : ℕ}
    (f : Signature AlgebraicComplex n) (hf : Generated F k f)
    (q : Fin r→Fin n) (hq : Function.Injective q)
    (hp : Function.Bijective (liveProjection f q)) :
    ∃ h : Signature AlgebraicComplex r,Generated F k h ∧ (∀ a,h a≠0) ∧
      ∀ x,f x≠0→h (fun j=>x (q j))=f x := by
  refine ⟨marginal f q,generated_marginal f hf q,?_,marginal_at_live f q hq hp.1⟩
  intro a
  obtain ⟨⟨x,hx⟩,ha⟩ := hp.2 a
  have he := marginal_at_live f q hq hp.1 x hx
  change (fun j=>x (q j))=a at ha
  rw [ha] at he
  rw [he]
  exact hx

end
end Paper2.DegreeCSP.GeneratedCoordinateMarginal
