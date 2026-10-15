import Paper2.DegreeCSP.RawData
import Paper2.DegreeCSP.Generated
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Records

/-! Literal ordered records expanding an opposite-pair binary lift. Each
partial-CSP copy keeps its original constraint and scope order; the added
disequality rows are repeated exactly k times. -/
namespace Paper2.DegreeCSP.QuarticLiftLayout
open Tractable
noncomputable section

abbrev Input := Holant.Complexity.FixedGadgetSubstitution.Compiler.Input 1 1 (fun _ => 4)
abbrev Vertex := Holant.Complexity.FixedGadgetSubstitution.Compiler.Query 1 1 (fun _ => 4)
abbrev inputEncoding := Holant.Complexity.RawClosedNetwork.validatedEncoding 1 1 (fun _ => 4)
abbrev vertexEncoding := Holant.Complexity.FixedGadgetSubstitution.Compiler.queryEncoding 1 1 (fun _ => 4)

def endpointAddress (p : Holant.Complexity.RawEndpoint) : ℕ :=
  2*p.1+(if p.2 then 1 else 0)

def sourcePort (x : Vertex) (i : ℕ) : Holant.Complexity.RawEndpoint :=
  (x.1.val.vertices.get x.2).2.getD i (0,false)

def hiddenAddress (P : Presentation AlgebraicComplex (Fin 2)) (x : Vertex) (h : Fin P.hiddenCount) : ℕ :=
  2*x.1.val.edges.length+x.2.val*P.hiddenCount+h.val

def scopeAddress (P : Presentation AlgebraicComplex (Fin 2)) (x : Vertex) :
    Fin 2 ⊕ Fin P.hiddenCount → ℕ :=
  Sum.elim (fun j => endpointAddress (sourcePort x (2*j.val))) (hiddenAddress P x)

def oldFactor (P : Presentation AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (x : Vertex) (c : Fin P.constraints) : ℕ × List ℕ :=
  (labels c,List.ofFn (fun i => scopeAddress P x (P.scope c i)))

def localFactor (label : ℕ) (x : Vertex) (j : Fin 2) : ℕ × List ℕ :=
  (label,[endpointAddress (sourcePort x (2*j.val)),
    endpointAddress (sourcePort x (2*j.val+1))])

def vertexFactors (P : Presentation AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (k label : ℕ) (x : Vertex) : List (ℕ × List ℕ) :=
  List.ofFn (oldFactor P labels x) ++
    (List.finRange 2).flatMap (fun j => List.replicate k (localFactor label x j))

def outerFactor (label e : ℕ) : ℕ × List ℕ := (label,[2*e,2*e+1])

def factors (P : Presentation AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (k label : ℕ) (r : Input) : List (ℕ × List ℕ) :=
  (List.finRange r.val.vertices.length).flatMap
      (fun v => vertexFactors P labels k label ⟨r,v⟩) ++
    (List.finRange r.val.edges.length).flatMap
      (fun e => List.replicate k (outerFactor label e.val))

def raw (P : Presentation AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (k label : ℕ) (r : Input) : Raw :=
  ⟨2*r.val.edges.length+r.val.vertices.length*P.hiddenCount,factors P labels k label r⟩

end
end Paper2.DegreeCSP.QuarticLiftLayout
