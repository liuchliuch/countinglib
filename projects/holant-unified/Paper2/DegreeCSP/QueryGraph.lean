import Paper2.DegreeCSP.EqualityDegreeTemplates
import Paper2.DegreeCSP.RawIncidence
import Paper2.DegreeCSP.FiniteSubstitution
import Paper2.DegreeCSP.OrderedEnumeration
import Paper2.Complexity.ClosedNetworkCompleteness

/-! The concrete degree-k compiler graph with prescribed row and edge indices.
Original rows come first. Variables and their gadget vertices retain the input
variable order. Occurrence edges precede every gadget's internal edges. -/
namespace Paper2.DegreeCSP.QueryGraph
open Paper2.Tractable Paper2.ExactInput Paper2.Complexity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

variable {s : ℕ} {a : ℕ → ℕ} {k : ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (hk : 3 ≤ k) (r : Raw.Input s a k)

def variableMacro (i : Fin r.val.variables) : Network AlgebraicComplex (Raw.degree r.val i.val) :=
  EqualityDegreeTemplates.make k hk _ (r.property.2.2 i.val i.isLt)

def replacement (v : Raw.IncidenceVertex r) :
    Network AlgebraicComplex (Raw.incidenceArity r v) :=
  match v with
  | .inl c => Network.corolla ((Raw.toInstance G r).table c)
  | .inr i => variableMacro hk r i

abbrev SubVertex := FiniteSubstitution.Vertices (Raw.incidence G r) (replacement G hk r)
abbrev SubInnerEdge := FiniteSubstitution.InnerEdges (Raw.incidence G r) (replacement G hk r)
abbrev SubEdge := FiniteSubstitution.Edges (Raw.incidence G r) (replacement G hk r)

abbrev ExtraVertex := Σ i : Fin r.val.variables,Fin (variableMacro hk r i).shape.vertices
abbrev InnerEdge := Σ i : Fin r.val.variables,Fin (variableMacro hk r i).shape.edges

def flattenVertices : SubVertex G hk r ≃ (Fin r.val.factors.length ⊕ ExtraVertex hk r) where
  toFun p := match p with
    | ⟨.inl c,_⟩ => .inl c
    | ⟨.inr i,v⟩ => .inr ⟨i,v⟩
  invFun p := match p with
    | .inl c => ⟨.inl c,(0 : Fin 1)⟩
    | .inr ⟨i,v⟩ => ⟨.inr i,v⟩
  left_inv := by
    rintro ⟨c | i,v⟩
    · change (⟨.inl c,(0 : Fin 1)⟩ : SubVertex G hk r) = ⟨.inl c,v⟩
      exact congrArg (fun j : Fin 1 => (⟨.inl c,j⟩ : SubVertex G hk r))
        (Subsingleton.elim _ _)
    · rfl
  right_inv := by rintro (c | ⟨i,v⟩) <;> rfl

def flattenInnerEdges : SubInnerEdge G hk r ≃ InnerEdge hk r where
  toFun p := match p with
    | ⟨.inl _,e⟩ => Fin.elim0 e
    | ⟨.inr i,e⟩ => ⟨i,e⟩
  invFun p := ⟨.inr p.1,p.2⟩
  left_inv := by
    rintro ⟨c | i,e⟩
    · exact Fin.elim0 e
    · rfl
  right_inv _ := rfl

def vertexCount := r.val.factors.length + ∑ i,(variableMacro hk r i).shape.vertices
def occurrenceCount := ∑ i : Fin r.val.variables,Raw.degree r.val i.val
def innerCount := ∑ i,(variableMacro hk r i).shape.edges
def edgeCount := occurrenceCount r + innerCount hk r

def vertexIndex : SubVertex G hk r ≃ Fin (vertexCount hk r) :=
  (flattenVertices G hk r).trans
    ((Equiv.sumCongr (Equiv.refl _) finSigmaFinEquiv).trans finSumFinEquiv)

def outerIndex : Raw.Ports r.val ≃ Fin (occurrenceCount r) :=
  (Raw.grouping r).trans finSigmaFinEquiv

def edgeIndex : SubEdge G hk r ≃ Fin (edgeCount hk r) :=
  (Equiv.sumCongr (outerIndex r)
    ((flattenInnerEdges G hk r).trans finSigmaFinEquiv)).trans finSumFinEquiv

def finiteGraph := FiniteSubstitution.graph (Raw.incidence G r) (replacement G hk r)

def network : Network AlgebraicComplex 0 :=
  OrderedEnumeration.graph (finiteGraph G hk r) (vertexIndex G hk r) (edgeIndex G hk r)

def vertexLabel (jK : Fin s) (p : SubVertex G hk r) : Fin s :=
  match p.1 with
  | .inl c => Raw.label r c
  | .inr _ => jK

theorem vertexLabel_arity (jK : Fin s) (hK : a jK.val = k) (p : SubVertex G hk r) :
    a (vertexLabel G hk r jK p).val = (finiteGraph G hk r).arity p := by
  rcases p with ⟨c | i,v⟩
  · exact (r.property.1 c).2.symm
  · change a jK.val = (variableMacro hk r i).shape.arity v
    exact hK.trans (EqualityDegreeTemplates.make_arity k hk _ (r.property.2.2 i.val i.isLt) v).symm

def labels (jK : Fin s) (hK : a jK.val = k) :
    ClosedLabelling (network G hk r).shape s 1 a where
  vertex v := vertexLabel G hk r jK ((vertexIndex G hk r).symm v)
  vertex_arity _ := vertexLabel_arity G hk r jK hK _
  edge _ := 0

def raw (jK : Fin s) (hK : a jK.val = k) : RawClosedNetwork :=
  (labels G hk r jK hK).serialize

theorem raw_valid (jK : Fin s) (hK : a jK.val = k) :
    (raw G hk r jK hK).WellFormed s 1 a :=
  (labels G hk r jK hK).serialize_wellFormed

theorem network_nativeX : (network G hk r).NativeX := by
  apply OrderedEnumeration.graph_nativeX
  apply FiniteSubstitution.graph_nativeX
  · exact Raw.incidence_nativeX G r
  · intro v
    cases v with
    | inl c => intro e; exact Fin.elim0 e
    | inr i => exact EqualityDegreeTemplates.make_nativeX k hk _ (r.property.2.2 i.val i.isLt)

theorem network_uses (F : SignatureFamily AlgebraicComplex)
    (hG : ∀ i,(⟨a i.val,G i⟩ : AnySignature AlgebraicComplex) ∈ F)
    (heq : (⟨k,equality k⟩ : AnySignature AlgebraicComplex) ∈ F) :
    (network G hk r).Uses F := by
  apply OrderedEnumeration.graph_uses
  rintro ⟨c | i,v⟩
  · exact Raw.instance_uses G r F hG c
  · exact EqualityDegreeTemplates.make_uses F _ _ _ _ heq v

end
end Paper2.DegreeCSP.QueryGraph
