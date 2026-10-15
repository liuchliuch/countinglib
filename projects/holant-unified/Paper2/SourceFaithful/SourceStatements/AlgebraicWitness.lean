import Paper2.Paper1ProvedCriteria
import Holant.Proofs.Algorithms.TransformRecognition.AffineBranch
import Holant.Proofs.Algorithms.TransformRecognition.ProductBranch
import Holant.Proofs.Algorithms.TransformRecognition.LocalAffineBranch
import Holant.Proofs.Algorithms.TransformRecognition.OriginalAffineSystem

/-! The mathematical descent clause of source Lemma 2.10. The original
common matrix, free scale and unary parameters are genuinely complex. The
edge is an arbitrary algebraic kernel, including singular kernels. The
result retains one algebraic matrix for that edge and every input table.
Effective discovery is a separate machine contract, not inferred from this
existence theorem or from classical decidability. -/
namespace Paper2.SourceFaithful.SourceStatements.AlgebraicWitness
set_option backward.isDefEq.respectTransparency false
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm
noncomputable section

inductive Class where
  | affine
  | product
  | localAffine

/-- Literal source normal forms, allowing arbitrary complex free parameters. -/
def ComplexMember (C : Class) {n : ℕ} (f : Holant.Signature ℂ n) : Prop :=
  match C with
  | .affine => ExtensionAffine.AffineOver (algebraMap Paper2.Tractable.AlgebraicComplex ℂ) f
  | .product => ExtensionSource.ProductOver f
  | .localAffine => ExtensionLocalAffine.LocalAffineOver
      (algebraMap Paper2.Tractable.AlgebraicComplex ℂ) f

def Member (C : Class) {n : ℕ}
    (f : Paper2.Signature Paper2.Tractable.AlgebraicComplex n) : Prop :=
  match C with
  | .affine => Paper2.Tractable.Affine f
  | .product => Paper2.Tractable.Product f
  | .localAffine => Paper2.Tractable.LocalAffine f

/-- An actual shared complex inverse pair; no algebraicity is imposed on it. -/
def ComplexWitness {s : ℕ} {arity : Fin s → ℕ} (C : Class)
    (G : (i : Fin s) → Paper2.Signature Paper2.Tractable.AlgebraicComplex (arity i))
    (E : Paper2.Kernel Paper2.Tractable.AlgebraicComplex) : Prop :=
  ∃ U V : Holant.Kernel ℂ,
    Holant.Kernel.mul U V = Holant.Signature.equality ∧
    Holant.Kernel.mul V U = Holant.Signature.equality ∧
    (∀ i, ComplexMember C
      (Holant.Signature.coordinateAction (fun _ => V) (fun x => (G i x : ℂ)))) ∧
    ComplexMember C (fun x : Fin 2 → Bool =>
      Holant.Kernel.pullback (fun a b => (E a b : ℂ)) U (x 0) (x 1))

def Witness {s : ℕ} {arity : Fin s → ℕ} (C : Class)
    (G : (i : Fin s) → Paper2.Signature Paper2.Tractable.AlgebraicComplex (arity i))
    (E : Paper2.Kernel Paper2.Tractable.AlgebraicComplex) : Prop :=
  ∃ U : Paper2.Tractable.InvertibleKernel,
    (∀ i, Member C (U.symm.action (G i))) ∧
    Member C (Paper2.Tractable.kernelSignature (Paper2.Kernel.pullback E U.matrix))

/-- Source 2.10: arbitrary complex common witnesses descend to one algebraic
common witness, with all original free normal-form parameters allowed. -/
theorem theorem_2_10_descent {s : ℕ} {arity : Fin s → ℕ} (C : Class)
    (G : (i : Fin s) → Paper2.Signature Paper2.Tractable.AlgebraicComplex (arity i))
    (E : Paper2.Kernel Paper2.Tractable.AlgebraicComplex)
    (h : ComplexWitness C G E) : Witness C G E := by
  cases C with
  | affine =>
    have hs : AffineBranch.Shared G E
        (algebraMap Paper2.Tractable.AlgebraicComplex ℂ) := h
    obtain ⟨U,hG,hE⟩ := AffineBranch.actual_basis G E (AffineBranch.descend G E hs)
    refine ⟨Paper2.Paper1Proved.invertibleKernelIso.symm U,?_,?_⟩
    · intro i
      exact (Paper2.Paper1Proved.affine_iff _).mpr (hG i)
    · exact (Paper2.Paper1Proved.affine_iff _).mpr hE
  | product =>
    obtain ⟨U,V,hUV,hVU,hG,hE⟩ := h
    have hs : ProductBranch.SharedSource G E
        (algebraMap Paper2.Tractable.AlgebraicComplex ℂ) := by
      refine ⟨U,V,hUV,hVU,?_⟩
      intro j
      cases j with
      | inl i => exact hG i
      | inr u => exact hE
    obtain ⟨U,hG,hE⟩ := ProductBranch.source_algebraic_basis G E hs
    refine ⟨Paper2.Paper1Proved.invertibleKernelIso.symm U,?_,?_⟩
    · intro i
      exact (Paper2.Paper1Proved.product_iff _).mpr (hG i)
    · exact (Paper2.Paper1Proved.product_iff _).mpr hE
  | localAffine =>
    obtain ⟨U,V,hUV,hVU,hG,hE⟩ := h
    have hs : LocalAffineBranch.Shared G E
        (algebraMap Paper2.Tractable.AlgebraicComplex ℂ) := by
      refine ⟨U,V,hUV,hVU,?_⟩
      intro j
      cases j with
      | inl i => exact hG i
      | inr u => exact hE
    obtain ⟨U,hG,hE⟩ := LocalAffineBranch.actual_basis G E (LocalAffineBranch.descend G E hs)
    refine ⟨Paper2.Paper1Proved.invertibleKernelIso.symm U,?_,?_⟩
    · intro i
      exact (Paper2.Paper1Proved.localAffine_iff _).mpr (hG i)
    · exact (Paper2.Paper1Proved.localAffine_iff _).mpr hE

section Input
variable {s : ℕ} (arity : Fin s → ℕ)

/-- Every original vertex entry, followed by the arbitrary original edge
entries in the same literal source catalogue. -/
def values
    (G : (i : Fin s) → Paper2.Signature Paper2.Tractable.AlgebraicComplex (arity i))
    (E : Paper2.Kernel Paper2.Tractable.AlgebraicComplex) :
    Fin (OriginalAffineSystem.Entries arity) → Paper2.Tractable.AlgebraicComplex :=
  fun k => match (LocalAffineVariableLayout.catalogue arity).get k with
    | ⟨.inl i,x⟩ => G i x
    | ⟨.inr _,x⟩ => E (x (0 : Fin 2)) (x (1 : Fin 2))

def input
    (g : (i : Fin s) → (Fin (arity i) → Bool) →
      Holant.LocalDrafts.EffectiveAlgebraic.RootCode)
    (e : Bool → Bool → Holant.LocalDrafts.EffectiveAlgebraic.RootCode) :
    OriginalAffineSystem.Input arity :=
  fun k => match (LocalAffineVariableLayout.catalogue arity).get k with
    | ⟨.inl i,x⟩ => g i x
    | ⟨.inr _,x⟩ => e (x (0 : Fin 2)) (x (1 : Fin 2))

@[simp] theorem sourceVertex_values
    (G : (i : Fin s) → Paper2.Signature Paper2.Tractable.AlgebraicComplex (arity i))
    (E : Paper2.Kernel Paper2.Tractable.AlgebraicComplex) :
    OriginalAffineSystem.sourceVertex arity (values arity G E) = G := by
  funext i x
  simp only [OriginalAffineSystem.sourceVertex,OriginalAffineSystem.entryIndex,
    values,LocalAffineVariableLayout.get_address]

@[simp] theorem sourceEdge_values
    (G : (i : Fin s) → Paper2.Signature Paper2.Tractable.AlgebraicComplex (arity i))
    (E : Paper2.Kernel Paper2.Tractable.AlgebraicComplex) :
    OriginalAffineSystem.sourceEdge arity (values arity G E) = E := by
  funext a b
  simp only [OriginalAffineSystem.sourceEdge,OriginalAffineSystem.entryIndex,
    values,LocalAffineVariableLayout.get_address,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.head_cons]

@[simp] theorem input_vertex
    (g : (i : Fin s) → (Fin (arity i) → Bool) →
      Holant.LocalDrafts.EffectiveAlgebraic.RootCode)
    (e : Bool → Bool → Holant.LocalDrafts.EffectiveAlgebraic.RootCode)
    (i : Fin s) (x : Fin (arity i) → Bool) :
    input arity g e (OriginalAffineSystem.entryIndex arity (.inl i) x) = g i x := by
  simp only [input,OriginalAffineSystem.entryIndex,LocalAffineVariableLayout.get_address]

@[simp] theorem input_edge
    (g : (i : Fin s) → (Fin (arity i) → Bool) →
      Holant.LocalDrafts.EffectiveAlgebraic.RootCode)
    (e : Bool → Bool → Holant.LocalDrafts.EffectiveAlgebraic.RootCode)
    (a b : Bool) :
    input arity g e (OriginalAffineSystem.entryIndex arity (.inr ()) ![a,b]) = e a b := by
  simp only [input,OriginalAffineSystem.entryIndex,LocalAffineVariableLayout.get_address,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.head_cons]

theorem input_represents
    (G : (i : Fin s) → Paper2.Signature Paper2.Tractable.AlgebraicComplex (arity i))
    (E : Paper2.Kernel Paper2.Tractable.AlgebraicComplex)
    (g : (i : Fin s) → (Fin (arity i) → Bool) →
      Holant.LocalDrafts.EffectiveAlgebraic.RootCode)
    (e : Bool → Bool → Holant.LocalDrafts.EffectiveAlgebraic.RootCode)
    (hG : ∀ i x, (g i x).Represents (G i x : ℂ))
    (hE : ∀ a b, (e a b).Represents (E a b : ℂ)) :
    ∀ k, (input arity g e k).Represents (values arity G E k : ℂ) := by
  intro k
  unfold input values
  generalize (LocalAffineVariableLayout.catalogue arity).get k = p
  rcases p with ⟨j,x⟩
  cases j with
  | inl i => exact hG i x
  | inr u => exact hE (x (0 : Fin 2)) (x (1 : Fin 2))

end Input

end
end Paper2.SourceFaithful.SourceStatements.AlgebraicWitness

