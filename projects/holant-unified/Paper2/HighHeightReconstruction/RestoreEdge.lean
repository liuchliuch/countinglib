import Paper2.HighHeightReconstruction.Projection

/-! Restore a contracted named pair to the actual residual matching. -/
namespace Paper2.HighHeightReconstruction
open CommonPhase EndpointSelfLoop MatchingPropagation
variable {ι : Type}

def restoreSlots (k : ℕ) : (Fin (k+1) × Bool) ≃ ((Fin k × Bool) ⊕ Bool) where
  toFun jb := Fin.cases (.inr jb.2) (fun j => .inl (j,jb.2)) jb.1
  invFun q := match q with
    | .inl (j,b) => (j.succ,b)
    | .inr b => (0,b)
  left_inv := by
    rintro ⟨j,b⟩
    refine Fin.cases ?_ (fun k => ?_) j <;> rfl
  right_inv := by
    intro q
    rcases q with ⟨j,b⟩ | b <;> rfl

/-- Add the deleted edge as factor zero and retain each residual factor's
actual orientation and original port occurrence. -/
noncomputable def restoreMatching (e : PortPair ι)
    (P : Matching (Remaining e.first e.second)) : Matching ι where
  count := P.count + 1
  ports := (restoreSlots P.count).trans
    ((Equiv.sumCongr P.ports (Equiv.refl Bool)).trans (splitPorts e.first e.second e.distinct).symm)

@[simp] theorem restoreMatching_first (e : PortPair ι)
    (P : Matching (Remaining e.first e.second)) (b : Bool) :
    (restoreMatching e P).ports ((0 : Fin (P.count+1)),b) = if b then e.second else e.first := by
  rfl

@[simp] theorem restoreMatching_succ (e : PortPair ι)
    (P : Matching (Remaining e.first e.second)) (j : Fin P.count) (b : Bool) :
    (restoreMatching e P).ports (j.succ,b) = (P.ports (j,b)).val := by
  rfl

theorem transversal_restore (e : PortPair ι)
    (P : Matching (Remaining e.first e.second)) (x : ι → Bool) :
    Transversal (restoreMatching e P) x ↔
      x e.second = !(x e.first) ∧ Transversal P (restrict e.first e.second x) := by
  change (∀ j : Fin (P.count+1), x ((restoreMatching e P).ports (j,true)) =
    !(x ((restoreMatching e P).ports (j,false)))) ↔ _
  simp [Fin.forall_fin_succ,Transversal,restrict]

theorem literal_restore (e : PortPair ι)
    (P : Matching (Remaining e.first e.second)) (x : ι → Bool) :
    literal (restoreMatching e P) ℂ x =
      Signature.disequality (x e.first) (x e.second) *
        literal P ℂ (restrict e.first e.second x) := by
  classical
  rw [literal,transversal_restore]
  by_cases h : Transversal P (restrict e.first e.second x)
  · simp only [h,and_true,literal,ite_true,mul_one]
    cases x e.first <;> cases x e.second <;> rfl
  · simp [h,literal]

/-- Once the projection equality is proved, an X-product loop reconstructs
the complete original matching with its exact one-half scalar. -/
theorem isX_of_eq_project (e : PortPair ι) (F : Tensor ℂ ι)
    (hF : F = project e F) (hloop : XAt F e) : IsX F := by
  obtain ⟨P,c,hc,he⟩ := hloop
  refine ⟨restoreMatching e P,c/2,div_ne_zero hc (by norm_num),?_⟩
  funext x
  rw [congrFun hF x]
  change (Signature.disequality (x e.first) (x e.second) / 2) * e.pairSum F x = _
  rw [PortPair.pairSum_eq_loop]
  change (Signature.disequality (x e.first) (x e.second) / 2) *
    contraction F e (restrict e.first e.second x) = _
  rw [he,literal_restore]
  ring

/-- A persistent actual deck edge reconstructs the original scalar X product. -/
theorem isX_of_persistent_edge [Fintype ι] (hn : 8 ≤ Fintype.card ι)
    (F : Tensor ℂ ι) (hF : Tensor.ChargeLayer F 0)
    (lam : PortPair ι → ℂ)
    (P : (r : PortPair ι) → Matching (Remaining r.first r.second))
    (hd : MatchingDeck F lam P) (hnz : ∀ r, lam r ≠ 0) (e : PortPair ι)
    (hp : ∀ (r : PortPair ι) (hre : r.Disjoint e),
      mate (P r) (r.residual e hre).first = (r.residual e hre).second) : IsX F :=
  isX_of_eq_project e F (persistent_edge_factor hn F hF lam P hd e hp)
    ⟨P e,lam e,hnz e,hd e⟩

end Paper2.HighHeightReconstruction
