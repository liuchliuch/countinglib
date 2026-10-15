import Paper2.SourceFaithful.PointMass
import Paper2.SourceFaithful.GadgetAugmentation
import Paper2.Tractable.Conformal.EOTransport
import Paper2.Tractable.Downward
import Holant.Proofs.Reductions.GeneralExtraction.SupportCaps

/-! Actual pins for a two-sided family of single Hamming layers.  A strictly
charged source row first produces a one-copy native self-loop carrier.  Only
the separately proved factor-extraction reduction is used to obtain a literal
unary from that carrier.  The completed rows then have explicit edgeless
networks over the retained dictionary. -/
namespace Paper2.SourceFaithful.SingleWeight
open Tractable ExactInput
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

private def ofPaper1 {n : ℕ} (N : Holant.Network AlgebraicComplex n) :
    Paper2.Network AlgebraicComplex n where
  shape := ⟨N.shape.vertices,N.shape.arity,N.shape.edges,N.shape.ports⟩
  vertex := N.vertex
  edge := N.edge

/-- Diagnostic charged support is consumed by the actual source loop theorem.
The returned graph keeps the original row and literal native-X edges. -/
theorem charged_carrier (L : Language) (b : Bool) {n d : ℕ}
    (f : Signature AlgebraicComplex n)
    (hmem : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ L.family)
    (hf : f ≠ 0) (hd : Signature.SingleLayer f d)
    (x : Fin n → Bool) (hx : f x ≠ 0)
    (hcharge : 0 < if b then Paper2.charge x else -Paper2.charge x) :
    ∃ m : ℕ, 0 < m ∧ ∃ c : AlgebraicComplex, c ≠ 0 ∧
      NetworkRealizable L.family (ChargeBridge.pointMass b m c) := by
  have hside : ∀ y, f y ≠ 0 →
      0 < Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.balance b y := by
    intro y hy
    have hxw := hd.weight_of_nezero hx
    have hyw := hd.weight_of_nezero hy
    cases b
    · rw [Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.balance_false]
      change 0 < -Paper2.charge y
      change 0 < -Paper2.charge x at hcharge
      unfold Paper2.charge at *
      omega
    · rw [Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.balance_true]
      change 0 < Paper2.charge y
      change 0 < Paper2.charge x at hcharge
      unfold Paper2.charge at *
      omega
  obtain ⟨m,hm,c,hc,N,huses,hX,_,hden⟩ :=
    Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps.strict_side_pin
      (by norm_num : (2 : AlgebraicComplex) ≠ 0) b f hf hside
  refine ⟨m,hm,c,hc,m,ofPaper1 N,Equiv.refl _,?_,?_,?_⟩
  · intro v
    have h := Set.mem_singleton_iff.mp (huses v)
    change (⟨N.shape.arity v,N.vertex v⟩ : AnySignature AlgebraicComplex) ∈ L.family
    rw [h]
    exact hmem
  · intro e
    exact hX e
  · exact hden

private theorem pointMass_ne_zero (b : Bool) {n : ℕ} (c : AlgebraicComplex)
    (hc : c ≠ 0) : ChargeBridge.pointMass b n c ≠ 0 := by
  intro h
  have hh := congrFun h (fun _ => b)
  exact hc (by simpa [ChargeBridge.pointMass] using hh)

/-- Both strict charge signs yield both literal pins through genuine retained
gadget and factor reductions.  No unary classification is used. -/
theorem both_pins (G : Paper1DirectGadgetAccepted) (Fac : Paper1FactorClosureAccepted)
    (L : Language) (hp : Preprocessed L.family)
    (hlayers : ∀ g ∈ L.family, ∃ d, Signature.SingleLayer g.2 d)
    (hboth : BothChargeSigns L.family) :
    ∃ N : Language, L.family ⊆ N.family ∧
      (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ N.family ∧
      (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ N.family ∧
      Preprocessed N.family ∧ FixedFieldOutput.Reduces .nativeX N L := by
  obtain ⟨f,hf,x,hx,hneg⟩ := hboth.1
  obtain ⟨g,hg,y,hy,hpos⟩ := hboth.2
  obtain ⟨df,hdf⟩ := hlayers f hf
  obtain ⟨dg,hdg⟩ := hlayers g hg
  obtain ⟨m,hm,c,hc,hC⟩ := charged_carrier L false f.2 hf (hp f hf).2 hdf x hx (by simpa using hneg)
  obtain ⟨n,hn,d,hd,hD⟩ := charged_carrier L true g.2 hg (hp g hg).2 hdg y hy hpos
  obtain ⟨A,hA,hAL⟩ := G.adjoin_pair L (ChargeBridge.pointMass false m c)
    (ChargeBridge.pointMass true n d)
    (NativeNetworkRealizesUpTo.of_realizable hC) (NativeNetworkRealizesUpTo.of_realizable hD)
  have hLA : L.family ⊆ A.family := by
    intro k hk
    rw [hA]
    exact Or.inr (Or.inr hk)
  have hpA : Preprocessed A.family := by
    rw [hA]
    intro k hk
    rcases hk with rfl | rfl | hk
    · exact ⟨hm,pointMass_ne_zero false c hc⟩
    · exact ⟨hn,pointMass_ne_zero true d hd⟩
    · exact hp k hk
  have ht : ¬ CommonOneSided A.family := by
    intro hside
    rcases hside with hside | hside
    · exact (not_le.mpr hneg) (hside f (hLA hf) x hx)
    · exact (not_le.mpr hpos) (hside g (hLA hg) y hy)
  obtain ⟨N,hAN,hzero,hone,hpN,_,hNA,_⟩ := pointMass_pair_factorClosure Fac A hpA ht
    hm hn c d hc hd
    (by rw [hA]; exact Or.inl rfl)
    (by rw [hA]; exact Or.inr (Or.inl rfl))
  exact ⟨N,hLA.trans hAN,hzero,hone,hpN,hNA.trans hAL⟩

private def pinArity (n m : ℕ) : Unit ⊕ Fin m → ℕ
  | .inl _ => n
  | .inr _ => 1

private def pinRows {n m : ℕ} (f : Signature AlgebraicComplex n) (b : Bool) :
    (v : Unit ⊕ Fin m) → Signature AlgebraicComplex (pinArity n m v)
  | .inl _ => f
  | .inr _ => TensorDecomposition.literalPin b

private def pinPorts (n m : ℕ) : (Σ v : Unit ⊕ Fin m, Fin (pinArity n m v)) ≃ Fin (n+m) where
  toFun p := match p with
    | ⟨.inl _,i⟩ => Fin.castAdd m i
    | ⟨.inr j,_⟩ => Fin.natAdd n j
  invFun k := Sum.elim (fun i => ⟨.inl (),i⟩)
    (fun j => ⟨.inr j,⟨0,by change 0 < 1; decide⟩⟩)
    ((finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n+m)).symm k)
  left_inv p := by
    rcases p with ⟨v,i⟩
    cases v with
    | inl u => cases u; simp
    | inr j =>
      have hi : i=(⟨0,by change 0 < 1; decide⟩ : Fin (pinArity n m (.inr j))) := Fin.eq_zero i
      subst i
      simp
  right_inv k := by
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k <;> simp

/-- Appending any ordered number of literal pins is an actual finite
edgeless network, including the case with no appended ports. -/
theorem append_pins_realizable (N : Language) {n : ℕ}
    (f : Signature AlgebraicComplex n)
    (hmem : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (b : Bool) (hpin : (⟨1,TensorDecomposition.literalPin b⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (m : ℕ) : NetworkRealizable N.family
      (Signature.tensor f (Signature.unaryPower (Signature.pointMass b) m)) := by
  have hrows : ∀ v : Unit ⊕ Fin m,
      (⟨pinArity n m v,pinRows f b v⟩ : AnySignature AlgebraicComplex) ∈ N.family := by
    intro v
    cases v
    · exact hmem
    · exact hpin
  have h := (NetworkRealizable.piTensor (pinArity n m) (pinRows f b) hrows).reindex (pinPorts n m)
  have he : Tensor.reindex (pinPorts n m) (Tensor.piTensor (pinRows f b)) =
      Signature.tensor f (Signature.unaryPower (Signature.pointMass b) m) := by
    funext x
    simp only [Tensor.reindex_apply,Tensor.piTensor,Fintype.prod_sum_type]
    simp [pinRows,pinPorts,pinArity,Signature.tensor_apply,Signature.unaryPower,
      TensorDecomposition.literalPin,Signature.pointMass]
  exact he ▸ h

/-- Every exact ordered completion uses only the original row and the two
retained literal pins. -/
theorem completion_realizable (N : Language) {n : ℕ}
    (f : Signature AlgebraicComplex n)
    (hmem : (⟨n,f⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (hzero : (⟨1,TensorDecomposition.literalPin false⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (hone : (⟨1,TensorDecomposition.literalPin true⟩ : AnySignature AlgebraicComplex) ∈ N.family)
    (d : ℕ) : NetworkRealizable N.family (Signature.completeToEO f d).2 := by
  by_cases hc : n ≤ 2*d
  · rw [Signature.completeToEO,if_pos hc]
    exact append_pins_realizable N f hmem false hzero (2*d-n)
  · rw [Signature.completeToEO,if_neg hc]
    exact append_pins_realizable N f hmem true hone (n-2*d)

end
end Paper2.SourceFaithful.SingleWeight
