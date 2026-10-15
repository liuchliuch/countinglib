import Paper2.DegreeCSP.QueryGraph
import Paper2.DegreeCSP.EqualityDegreeSemantics

/-! Literal partition preservation of the compiler's physical graph and its
serialized query. Only a literal Eq_k table in the output dictionary is used. -/
namespace Paper2.DegreeCSP.QueryGraph
open Paper2.Tractable Paper2.ExactInput Paper2.Complexity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {a : ℕ → ℕ} {k : ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (hk : 3 ≤ k) (r : Raw.Input s a k)

theorem variableMacro_denote (i : Fin r.val.variables) :
    (variableMacro hk r i).denote = equality (Raw.degree r.val i.val) :=
  EqualityDegreeTemplates.make_denote _ _ _ _

theorem replacement_denote (v : Raw.IncidenceVertex r) :
    (replacement G hk r v).denote = (Raw.incidence G r).vertex v := by
  cases v with
  | inl c => exact Network.denote_corolla _
  | inr i => exact variableMacro_denote hk r i

theorem network_partition : (network G hk r).denote Fin.elim0 = Raw.value G r := by
  rw [network,OrderedEnumeration.graph_denote,finiteGraph]
  rw [FiniteSubstitution.graph_denote _ _ (Raw.incidence_nativeX G r) ?_
    (replacement_denote G hk r)]
  · exact Raw.incidence_partition G r
  · intro v
    cases v with
    | inl c => intro e; exact Fin.elim0 e
    | inr i => exact EqualityDegreeTemplates.make_nativeX k hk _ (r.property.2.2 i.val i.isLt)

private theorem castSignature_heq {n m : ℕ} (h : n=m) (f : Signature AlgebraicComplex m) :
    HEq (fun x : Fin n → Bool => f (fun j => x (Fin.cast h.symm j))) f := by
  cases h
  rfl

theorem vertexLabel_table (jK : Fin s)
    (hK : (⟨a jK.val,G jK⟩ : AnySignature AlgebraicComplex) = ⟨k,equality k⟩)
    (p : SubVertex G hk r) :
    (⟨(finiteGraph G hk r).arity p,(finiteGraph G hk r).vertex p⟩ : AnySignature AlgebraicComplex) =
      ⟨a (vertexLabel G hk r jK p).val,G (vertexLabel G hk r jK p)⟩ := by
  rcases p with ⟨c | i,v⟩
  · exact Sigma.ext (r.property.1 c).2
      (castSignature_heq (r.property.1 c).2 (G (Raw.label r c)))
  · exact (EqualityDegreeTemplates.make_vertex _ _ _ _ v).trans hK.symm

private theorem signature_cast_apply {n m : ℕ}
    (f : Signature AlgebraicComplex n) (g : Signature AlgebraicComplex m)
    (h : (⟨n,f⟩ : AnySignature AlgebraicComplex) = ⟨m,g⟩) (he : m=n) (x : Fin n → Bool) :
    g (fun j => x (Fin.cast he j)) = f x := by
  cases h
  rfl

theorem labelled_vertex (jK : Fin s)
    (hK : (⟨a jK.val,G jK⟩ : AnySignature AlgebraicComplex) = ⟨k,equality k⟩)
    (v : Fin (network G hk r).shape.vertices)
    (x : Fin ((network G hk r).shape.arity v) → Bool) :
    ((labels G hk r jK (congrArg Sigma.fst hK)).sourceNetwork G
      (fun _ : Fin 1 => Signature.disequality)).vertex v x = (network G hk r).vertex v x := by
  exact signature_cast_apply _ _
    (vertexLabel_table G hk r jK hK ((vertexIndex G hk r).symm v))
    (vertexLabel_arity G hk r jK (congrArg Sigma.fst hK) _) x

theorem raw_partition (jK : Fin s)
    (hK : (⟨a jK.val,G jK⟩ : AnySignature AlgebraicComplex) = ⟨k,equality k⟩) :
    ((raw G hk r jK (congrArg Sigma.fst hK)).realize
      (raw_valid G hk r jK (congrArg Sigma.fst hK)) G
      (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 = Raw.value G r := by
  change (((labels G hk r jK (congrArg Sigma.fst hK)).serialize).realize
    (labels G hk r jK (congrArg Sigma.fst hK)).serialize_wellFormed G
    (fun _ : Fin 1 => Signature.disequality)).denote Fin.elim0 = _
  rw [ClosedLabelling.denote_serialize]
  calc
    _ = (network G hk r).denote Fin.elim0 := by
      unfold Network.denote
      apply Finset.sum_congr rfl
      intro z _
      apply congrArg₂ (· * ·)
      · apply Finset.prod_congr rfl
        intro v _
        exact labelled_vertex G hk r jK hK v _
      · apply Finset.prod_congr rfl
        intro e _
        have he := network_nativeX G hk r e
        rw [he]
        rfl
    _ = Raw.value G r := network_partition G hk r

end
end Paper2.DegreeCSP.QueryGraph
