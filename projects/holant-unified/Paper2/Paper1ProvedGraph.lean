import Paper2.Problem
import Holant.Proofs.Algorithms.OriginalFamily

/-! The literal interface to the proved Paper 1 project. The two projects use
independent graph record types, so this module records the actual translation.
No graph transformation, coefficient change or encoding conversion is used. -/
namespace Paper2.Paper1Proved
open Paper2.Tractable Paper2.ExactInput Paper2.Complexity
noncomputable section

private theorem frame_bytes (bits : List Bool) :
    Holant.Algebraic.frame bits = Paper2.Algebraic.frame bits := by
  induction bits with
  | nil => rfl
  | cons b bits ih => simp only [Holant.Algebraic.frame,Paper2.Algebraic.frame,ih]

private theorem product_bytes {A B : Type} (ha pa : Computability.Encoding A Bool)
    (hb pb : Computability.Encoding B Bool)
    (heA : ∀ a,ha.encode a = pa.encode a) (heB : ∀ b,hb.encode b = pb.encode b)
    (v : A × B) :
    (Holant.Complexity.framedProductEncoding ha hb).encode v =
      (Paper2.Complexity.framedProductEncoding pa pb).encode v := by
  change Holant.Algebraic.frame (ha.encode v.1) ++ hb.encode v.2 =
    Paper2.Algebraic.frame (pa.encode v.1) ++ pb.encode v.2
  rw [heA,heB,frame_bytes]

private theorem list_bytes {A : Type} (h p : Computability.Encoding A Bool)
    (he : ∀ a,h.encode a = p.encode a) (vs : List A) :
    (Holant.Complexity.framedListEncoding h).encode vs =
      (Paper2.Complexity.framedListEncoding p).encode vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    change true :: (Holant.Algebraic.frame (h.encode v) ++
      (Holant.Complexity.framedListEncoding h).encode vs) =
      true :: (Paper2.Algebraic.frame (p.encode v) ++
      (Paper2.Complexity.framedListEncoding p).encode vs)
    rw [he,frame_bytes,ih]

private theorem endpoint_bytes (v : RawEndpoint) :
    Holant.Complexity.RawClosedNetwork.endpointEncoding.encode v =
      RawClosedNetwork.endpointEncoding.encode v :=
  product_bytes _ _ _ _ (fun _ => rfl) (fun _ => rfl) v

private theorem vertex_bytes (v : RawVertex) :
    Holant.Complexity.RawClosedNetwork.vertexEncoding.encode v =
      RawClosedNetwork.vertexEncoding.encode v :=
  product_bytes _ _ _ _ (fun _ => rfl) (list_bytes _ _ endpoint_bytes) v

/-- Algebraic coefficients and ordered tensor tables have the identical carrier. -/
abbrev signatures (L : Language) :
    (i : Fin L.count) → Holant.Signature Holant.Tractable.AlgebraicComplex (L.arity i.val) :=
  L.signature

/-- Preserve both ordered lists, including loop endpoints and nullary vertices. -/
def rawGraph (G : RawClosedNetwork) : Holant.Complexity.RawClosedNetwork :=
  ⟨G.vertices, G.edges⟩

def rawGraphIso : RawClosedNetwork ≃ Holant.Complexity.RawClosedNetwork where
  toFun := rawGraph
  invFun G := ⟨G.vertices,G.edges⟩
  left_inv _ := rfl
  right_inv _ := rfl

@[simp] theorem rawGraph_wellFormed (G : RawClosedNetwork) (s b : ℕ) (a : ℕ → ℕ) :
    (rawGraph G).WellFormed s b a ↔ G.WellFormed s b a := Iff.rfl

/-- A validated Paper 2 input supplies exactly a validated Paper 1 input. -/
def input (L : Language) (G : Problem.Instance L) :
    {r : Holant.Complexity.RawClosedNetwork // r.WellFormed L.count 1 L.arity} :=
  ⟨rawGraph G.val, G.property⟩

def inputIso (L : Language) : Problem.Instance L ≃
    {r : Holant.Complexity.RawClosedNetwork // r.WellFormed L.count 1 L.arity} where
  toFun := input L
  invFun G := ⟨rawGraphIso.symm G.val,G.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Even the bytes agree: the adapter requires no preprocessing machine. -/
theorem input_bytes (L : Language) (G : Problem.Instance L) :
    (Holant.Complexity.RawClosedNetwork.validatedEncoding L.count 1 L.arity).encode
      (input L G) = (Problem.inputEncoding L).encode G :=
  product_bytes _ _ _ _ (list_bytes _ _ vertex_bytes)
    (list_bytes _ _ (fun _ => rfl)) (G.val.vertices,G.val.edges)

theorem input_bytes_back (L : Language)
    (G : {r : Holant.Complexity.RawClosedNetwork // r.WellFormed L.count 1 L.arity}) :
    (Holant.Complexity.RawClosedNetwork.validatedEncoding L.count 1 L.arity).encode G =
      (Problem.inputEncoding L).encode ((inputIso L).symm G) := by
  have h := input_bytes L ((inputIso L).symm G)
  change (Holant.Complexity.RawClosedNetwork.validatedEncoding L.count 1 L.arity).encode
    ((inputIso L) ((inputIso L).symm G)) = _ at h
  rwa [Equiv.apply_symm_apply] at h

def kernels (w : Problem.Wiring) : Fin 1 → Holant.Kernel AlgebraicComplex :=
  fun _ => w.kernel

/-- The literal ordered finite sum agrees across the two independent records. -/
theorem network_value (w : Problem.Wiring) (L : Language) (G : Problem.Instance L) :
    ((input L G).val.realize (input L G).property (signatures L) (kernels w)).denote
      Fin.elim0 = Problem.value w L G := rfl

/-- The chosen-field answer of the actual proved Paper 1 algorithm is the
original Paper 2 answer. Output coordinate transport is handled separately. -/
theorem value (w : Problem.Wiring) (L : Language) (G : Problem.Instance L) :
    (Holant.LocalDrafts.MainChain.OriginalFamily.value (signatures L) (kernels w)
      (input L G) : AlgebraicComplex) = Problem.value w L G := by
  rw [Holant.LocalDrafts.MainChain.OriginalFamily.value_exact]
  exact network_value w L G

@[simp] theorem family (L : Language) :
    Set.range (fun i => (⟨L.arity i.val, signatures L i⟩ :
      Holant.AnySignature Holant.Tractable.AlgebraicComplex)) = L.family := rfl

end
end Paper2.Paper1Proved
