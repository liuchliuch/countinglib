import Paper2.HeightOne.PhaseCards.Augmentation
import Paper2.HeightOne.PhaseCards.FiniteRecursion

/-! Finite recursive processing of the actual ordered cards for a fixed finite
binary menu. Both orientations, every ordered distinct pair, and a genuine
selected prime factorization are included. -/
set_option backward.isDefEq.respectTransparency false
namespace Paper2.HeightOne.PhaseCards
noncomputable section
open Tractable GroupSplit GroupSplit.MatrixGroup EndpointSelfLoop

structure BinaryMenu (F : SignatureFamily AlgebraicComplex) where
  count : ℕ
  binary : Fin count → AMat
  actual : ∀ i, ActualNonsingular F (binary i)

/-- A finite menu of witnesses for every class of the complete actual group.
The menu records witnesses; it does not define or replace that group. -/
theorem complete_binaryMenu {F : SignatureFamily AlgebraicComplex}
    (hfinite : (actualClasses F).Finite) :
    ∃ M : BinaryMenu F, ∀ q ∈ actualClasses F, ∃ i,
      projectiveClass (transfer (M.binary i)) = pglToProjectiveClass q := by
  letI : Fintype (actualClasses F) := hfinite.fintype
  obtain ⟨rep, hrep⟩ := fixed_actualClass_representatives F
  let M : BinaryMenu F := ⟨Fintype.card (actualClasses F),
    (fun i => rep ((Fintype.equivFin (actualClasses F)).symm i)),
    (fun i => (hrep _).1)⟩
  refine ⟨M, ?_⟩
  intro q hq
  refine ⟨(Fintype.equivFin (actualClasses F)) ⟨q, hq⟩, ?_⟩
  simpa only [M, Equiv.symm_apply_apply] using (hrep ⟨q, hq⟩).2

lemma networkRealizable_mono {F G : SignatureFamily AlgebraicComplex}
    (hFG : F ⊆ G) {ι : Type} {f : Tensor AlgebraicComplex ι}
    (hf : NetworkRealizable F f) : NetworkRealizable G f := by
  obtain ⟨n, N, e, hU, hX, he⟩ := hf
  exact ⟨n, N, e, fun v => hFG (hU v), hX, he⟩

namespace BinaryMenu
variable {F : SignatureFamily AlgebraicComplex} (M : BinaryMenu F)

abbrev Choices (f : AnySignature AlgebraicComplex) :=
  {p : Fin f.1 × Fin f.1 // p.1 ≠ p.2} × Fin M.count × Bool

instance (f : AnySignature AlgebraicComplex) : Fintype (M.Choices f) := by
  classical
  infer_instance

def oriented (i : Fin M.count) (rev : Bool) : AMat :=
  if rev then (M.binary i).transpose else M.binary i

lemma oriented_actual (i : Fin M.count) (rev : Bool) : ActualNonsingular F (M.oriented i rev) := by
  cases rev
  · exact M.actual i
  · exact actualNonsingular_transpose (M.actual i)

/-- An actual oriented card, retained as a literal ordered finite signature. -/
def produced (f : AnySignature AlgebraicComplex) (k : M.Choices f) : AnySignature AlgebraicComplex :=
  let a := k.1.val.1
  let b := k.1.val.2
  ⟨Fintype.card (Remaining a b), Tensor.reindex (Fintype.equivFin (Remaining a b))
    (card (nativeKernel (M.oriented k.2.1 k.2.2)) a b k.1.property f.2)⟩

lemma produced_arity (f : AnySignature AlgebraicComplex) (k : M.Choices f) :
    (M.produced f k).1 + 2 = f.1 := by
  simpa only [produced, Fintype.card_fin] using remaining_card k.1.val.1 k.1.val.2 k.1.property

/-- Actualness remains valid at every retained enlargement. The fixed menu's
witnesses are merely relabelled into the larger resource family. -/
theorem produced_realizable {G : SignatureFamily AlgebraicComplex} (hFG : F ⊆ G)
    (f : AnySignature AlgebraicComplex) (hf : f ∈ G) (k : M.Choices f) :
    NetworkRealizable G (M.produced f k).2 := by
  dsimp only [produced, card]
  apply NetworkRealizable.reindex
  apply actual_contractKernel
  · exact (networkRealizable_of_mem hf).reindex _
  · exact networkRealizable_mono hFG (M.oriented_actual k.2.1 k.2.2).1

end BinaryMenu

/-- A genuine chosen decomposition, only for nonzero positive-arity cards. -/
def selectedDecomposition (f : AnySignature AlgebraicComplex)
    (hf : 0 < f.1 ∧ f.2 ≠ 0) : TensorDecomposition AlgebraicComplex f.1 :=
  Classical.choose (exists_prime_decomposition f.2 hf.1 hf.2)

lemma selectedDecomposition_spec (f : AnySignature AlgebraicComplex)
    (hf : 0 < f.1 ∧ f.2 ≠ 0) :
    (selectedDecomposition f hf).value = f.2 ∧
    (∀ i, 0 < (selectedDecomposition f hf).arity i) ∧
    (∀ i, TensorPrime ((selectedDecomposition f hf).factor i)) :=
  Classical.choose_spec (exists_prime_decomposition f.2 hf.1 hf.2)

/-- Zero and nullary cards have no positive factors to recurse on. -/
def selectedFactors (f : AnySignature AlgebraicComplex) : Set (AnySignature AlgebraicComplex) :=
  if hf : 0 < f.1 ∧ f.2 ≠ 0 then
    Set.range (fun i : Fin (selectedDecomposition f hf).count =>
      (⟨(selectedDecomposition f hf).arity i, (selectedDecomposition f hf).factor i⟩ :
        AnySignature AlgebraicComplex))
  else ∅

lemma selectedFactors_finite (f : AnySignature AlgebraicComplex) : (selectedFactors f).Finite := by
  unfold selectedFactors
  split_ifs
  · exact Set.finite_range _
  · exact Set.finite_empty

lemma selectedFactors_properties {f g : AnySignature AlgebraicComplex}
    (hg : g ∈ selectedFactors f) : 0 < g.1 ∧ TensorPrime g.2 ∧ g.1 ≤ f.1 := by
  unfold selectedFactors at hg
  split_ifs at hg with hf
  · obtain ⟨i, rfl⟩ := hg
    exact ⟨(selectedDecomposition_spec f hf).2.1 i,
      (selectedDecomposition_spec f hf).2.2 i, factor_arity_le _ i⟩
  · exact False.elim hg

namespace BinaryMenu
variable {F : SignatureFamily AlgebraicComplex} (M : BinaryMenu F)

/-- Every fixed representative, both orientations, and every ordered distinct
port pair are processed, with their actual selected positive prime factors. -/
def children (f : AnySignature AlgebraicComplex) : Set (AnySignature AlgebraicComplex) :=
  ⋃ k : M.Choices f, selectedFactors (M.produced f k)

lemma children_finite (f : AnySignature AlgebraicComplex) : (M.children f).Finite :=
  Set.finite_iUnion (fun k => selectedFactors_finite (M.produced f k))

lemma child_arity {f g : AnySignature AlgebraicComplex} (hg : g ∈ M.children f) :
    0 < g.1 ∧ TensorPrime g.2 ∧ g.1 + 2 ≤ f.1 := by
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hg
  obtain ⟨hp, ht, hn⟩ := selectedFactors_properties hk
  have ha := M.produced_arity f k
  exact ⟨hp, ht, by omega⟩

/-- The actual selected card/factor recursion has finite exhaustive closure.
No group-invariance or complexity classification is hidden in this conclusion. -/
theorem finite_factor_subtree (S : Set (AnySignature AlgebraicComplex)) (hS : S.Finite) :
    ∃ T : Set (AnySignature AlgebraicComplex), T.Finite ∧ S ⊆ T ∧
      (∀ f ∈ T, M.children f ⊆ T) ∧
      (∀ g ∈ T, ∃ f ∈ S, Relation.ReflTransGen (fun a b => b ∈ M.children a) f g) := by
  exact finite_recursive_closure (fun f => f.1) (fun a b => b ∈ M.children a)
    M.children_finite (fun a b h => by have := M.child_arity h; omega) S hS

end BinaryMenu
end
end Paper2.HeightOne.PhaseCards
