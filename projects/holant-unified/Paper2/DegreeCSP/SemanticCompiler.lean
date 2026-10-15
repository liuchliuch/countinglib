import Paper2.DegreeCSP.Incidence

/-! Actual ordered macro substitution for the incidence graph. A replacement
is a finite native-X graph with its literal vertex labels and exact boundary
value. The compiler keeps all outer occurrence edges and independently inlines
each replacement's internal edges. No oracle access is used as graph access. -/
namespace Paper2.DegreeCSP
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Instance
variable {K : Type} [CommSemiring K] (I : Instance K)

abbrev IncidenceVertex := Fin I.constraints ⊕ Fin I.variableCount

structure Replacement (F : SignatureFamily K) where
  graph : (v : I.IncidenceVertex) → Network K (I.incidenceArity v)
  uses : ∀ v, (graph v).Uses F
  nativeX : ∀ v, (graph v).NativeX
  value : ∀ v, (graph v).denote = I.incidence.vertex v

def Replacement.ordered {F : SignatureFamily K} (R : I.Replacement F)
    (v : Fin I.incidenceNetwork.shape.vertices) :
    Network K (I.incidenceNetwork.shape.arity v) :=
  R.graph ((Fintype.equivFin I.IncidenceVertex).symm v)

def compile {F : SignatureFamily K} (R : I.Replacement F) : Network K 0 :=
  I.incidenceNetwork.substitute (R.ordered I)

theorem compile_uses {F : SignatureFamily K} (R : I.Replacement F) :
    (I.compile R).Uses F := by
  apply Network.substitute_uses
  intro v
  exact R.uses _

theorem compile_nativeX {F : SignatureFamily K} (R : I.Replacement F) :
    (I.compile R).NativeX := by
  apply Network.substitute_nativeX _ _ I.incidenceNetwork_nativeX
  intro v
  exact R.nativeX _

theorem compile_denote {F : SignatureFamily K} (R : I.Replacement F) :
    (I.compile R).denote = I.incidenceNetwork.denote := by
  apply Network.denote_substitute _ _ I.incidenceNetwork_nativeX
    (fun _ => R.nativeX _) (fun _ => R.value _)

theorem compile_partition {F : SignatureFamily K} (R : I.Replacement F) :
    (I.compile R).denote Fin.elim0 = I.partition := by
  rw [I.compile_denote R]
  exact I.incidenceNetwork_partition

/-- Choosing only actual finite witnesses supplies concrete replacement data;
the semantic compiler itself is the explicit graph substitution above. -/
def replacementOfRealizable (F : SignatureFamily K)
    (h : ∀ v : I.IncidenceVertex, NetworkRealizable F (I.incidence.vertex v)) :
    I.Replacement F where
  graph v := Classical.choose ((h v).ordered)
  uses v := (Classical.choose_spec ((h v).ordered)).1
  nativeX v := (Classical.choose_spec ((h v).ordered)).2.1
  value v := (Classical.choose_spec ((h v).ordered)).2.2

theorem partition_realizable (F : SignatureFamily K)
    (h : ∀ v : I.IncidenceVertex, NetworkRealizable F (I.incidence.vertex v)) :
    NetworkRealizable F (fun _ : Fin 0 → Bool => I.partition) := by
  let R := I.replacementOfRealizable F h
  refine ⟨0,I.compile R,Equiv.refl _,I.compile_uses R,I.compile_nativeX R,?_⟩
  simp only [Tensor.reindex_refl]
  funext x
  have hx : x = Fin.elim0 := funext (fun i => Fin.elim0 i)
  rw [hx]
  exact I.compile_partition R

end Instance
end
end Paper2.DegreeCSP
