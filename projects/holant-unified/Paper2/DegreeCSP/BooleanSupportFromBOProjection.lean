import Paper2.DegreeCSP.BooleanSupportFromBOCancellation
import Paper2.DegreeCSP.GeneratedPullback

/-! Actual generated support closure under Boolean existential projection and
finite conjunction. Dyadic powering prevents accidental cancellations in every
retained row; each witness is built by the proved presentation constructors. -/
namespace Paper2.DegreeCSP.BooleanSupportFromBO
open scoped BigOperators
open Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- One literal hidden Boolean variable realizes the existential support after
one common genuine power of the input table. -/
theorem generated_exists_last {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    {f : Signature AlgebraicComplex (n+1)} (hf : Generated F k f) :
    ∃ g : Signature AlgebraicComplex n,Generated F k g ∧
      ∀ x,g x≠0 ↔ ∃ b : Bool,f (Fin.snoc x b)≠0 := by
  classical
  obtain ⟨N,hN⟩ := exists_uniform_power
    (fun x => f (Fin.snoc x false)) (fun x => f (Fin.snoc x true))
  let g : Signature AlgebraicComplex n := fun x => ∑ b : Bool,f (Fin.snoc x b)^(2^N)
  refine ⟨g,generated_sum_last (generated_pow hf (2^N)),?_⟩
  intro x
  have he : g x=f (Fin.snoc x false)^(2^N)+f (Fin.snoc x true)^(2^N) := by
    simp [g,add_comm]
  rw [he]
  simpa only [Bool.exists_bool] using hN x

/-- Successive actual existential steps eliminate any finite Boolean suffix.
The support witnesses retain every assignment in the original relation. -/
theorem generated_exists_suffix {F : SignatureFamily AlgebraicComplex} {k m n : ℕ}
    {f : Signature AlgebraicComplex (m+n)} (hf : Generated F k f) :
    ∃ g : Signature AlgebraicComplex m,Generated F k g ∧
      ∀ x,g x≠0 ↔ ∃ y : Fin n→Bool,f (Fin.append x y)≠0 := by
  induction n with
  | zero =>
    refine ⟨f,hf,?_⟩
    intro x
    constructor
    · intro hx
      refine ⟨Fin.elim0,?_⟩
      rw [show Fin.append x Fin.elim0=x from Fin.append_right_nil x Fin.elim0 rfl]
      exact hx
    · rintro ⟨y,hy⟩
      rw [show Fin.append x y=x from Fin.append_right_nil x y rfl] at hy
      exact hy
  | succ n ih =>
    obtain ⟨g,hg,hgs⟩ := generated_exists_last hf
    obtain ⟨h,hh,hhs⟩ := ih hg
    refine ⟨h,hh,?_⟩
    intro x
    rw [hhs]
    constructor
    · rintro ⟨y,hy⟩
      obtain ⟨b,hb⟩ := (hgs (Fin.append x y)).mp hy
      exact ⟨Fin.snoc y b,by simpa only [Fin.append_snoc] using hb⟩
    · rintro ⟨y,hy⟩
      obtain ⟨⟨b,z⟩,rfl⟩ := (Fin.snocEquiv (fun _ : Fin (n+1)=>Bool)).surjective y
      refine ⟨z,(hgs (Fin.append x z)).mpr ⟨b,?_⟩⟩
      change f (Fin.append x (Fin.snoc z b))≠0 at hy
      simpa only [Fin.append_snoc] using hy

/-- Finite products use disjoint copies of each real presentation. -/
theorem generated_product {F : SignatureFamily AlgebraicComplex} {k n : ℕ}
    {ι : Type} [Fintype ι] (g : ι→Signature AlgebraicComplex n)
    (hg : ∀ i,Generated F k (g i)) : Generated F k (fun x=>∏ i,g i x) := by
  classical
  have h : ∀ s : Finset ι,Generated F k (fun x=>∏ i∈s,g i x) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using generated_one F k n
    | @insert i s hi ih =>
      simpa only [Finset.prod_insert hi] using generated_hadamard (hg i) ih
  simpa using h Finset.univ

/-- Scope maps may identify coordinates. Every conjunct remains an actual
factor, and the nonzero product is exactly relational conjunction. -/
theorem generated_conjunction {F : SignatureFamily AlgebraicComplex} {k m : ℕ}
    {ι : Type} [Fintype ι] (a : ι→ℕ) (f : (i : ι)→Signature AlgebraicComplex (a i))
    (hf : ∀ i,Generated F k (f i)) (scope : (i : ι)→Fin (a i)→Fin m) :
    Generated F k (fun x=>∏ i,f i (fun j=>x (scope i j))) :=
  generated_product _ (fun i=>generated_pullback (hf i) (scope i))

theorem conjunction_support {m : ℕ} {ι : Type} [Fintype ι]
    (a : ι→ℕ) (f : (i : ι)→Signature AlgebraicComplex (a i))
    (scope : (i : ι)→Fin (a i)→Fin m) (x : Fin m→Bool) :
    (∏ i,f i (fun j=>x (scope i j)))≠0 ↔ ∀ i,f i (fun j=>x (scope i j))≠0 := by
  classical
  simp only [Finset.prod_ne_zero_iff,Finset.mem_univ,true_implies]

end
end Paper2.DegreeCSP.BooleanSupportFromBO
