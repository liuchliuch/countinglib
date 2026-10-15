import Paper2.Paper1ProvedPinDeletion
import Paper2.NetworkSubstitution

/-! The exact ordered deletion graph also accepts a previously constructed
source network. Vertex substitution inlines that network, so repeated pin caps
continue to use only the original resource family and literal native X edges. -/
namespace Paper2.Paper1Proved.PinDeletion
open Paper2.Tractable Paper2.ExactInput
noncomputable section

theorem member_realizable_family (F : SignatureFamily AlgebraicComplex) {m : ℕ}
    (f : Signature AlgebraicComplex m)
    (hf : (⟨m,f⟩ : AnySignature AlgebraicComplex) ∈ F) : NetworkRealizable F f := by
  refine ⟨m,Network.corolla f,Equiv.refl _,?_,?_,?_⟩
  · intro v
    exact hf
  · intro e
    exact Fin.elim0 e
  · simpa only [Tensor.reindex_refl] using Network.denote_corolla f

theorem pinCoordinate_of_realizable_family (F : SignatureFamily AlgebraicComplex) {n : ℕ}
    (f : Signature AlgebraicComplex (n+1)) (i : Fin (n+1)) (b : Bool)
    (hf : NetworkRealizable F f)
    (hpin : (⟨1,TensorDecomposition.literalPin (!b)⟩ : AnySignature AlgebraicComplex) ∈ F) :
    NetworkRealizable F (pinCoordinate f i b) := by
  let G := (finite f i b).toNetwork
  have hv : ∀ v, NetworkRealizable F (G.vertex v) := by
    intro v
    change NetworkRealizable F
      ((finite f i b).vertex ((Fintype.equivFin Bool).symm v))
    cases (Fintype.equivFin Bool).symm v with
    | false => exact hf
    | true => exact member_realizable_family F _ hpin
  have hg := NetworkRealizable.substitute G (by intro e; rfl) hv
  have hd : G.denote=pinCoordinate f i b := by
    dsimp only [G]
    rw [FiniteNetwork.denote_toNetwork,finite_denote]
  exact hd ▸ hg

theorem pinCoordinate_of_realizable (L : Language) {n : ℕ}
    (f : Signature AlgebraicComplex (n+1)) (i : Fin (n+1)) (b : Bool)
    (hf : NetworkRealizable L.family f)
    (hpin : (⟨1,TensorDecomposition.literalPin (!b)⟩ : AnySignature AlgebraicComplex) ∈ L.family) :
    NetworkRealizable L.family (pinCoordinate f i b) :=
  pinCoordinate_of_realizable_family L.family f i b hf hpin

end
end Paper2.Paper1Proved.PinDeletion
