import ComplexCSP.Complexity.GadgetSubstitutionSemantics

/-! # Decode a nonempty raw instance with its first variable as the single root -/
namespace ComplexCSP.RootedCSPCodePresentation
open ComplexityCSPCode ComplexityGadgetSubstitution
open scoped BigOperators
variable {D K : Type} {s : ℕ} (L : Language D K (Fin s))

def split (n : ℕ) (hn : 0 < n) : Fin n ≃ (Fin 1 ⊕ Fin (n-1)) :=
  (finCongr (by omega : n = 1+(n-1))).trans finSumFinEquiv.symm

def decode (g : Code) (hg : Valid L g) (hn : 0 < g.vertices) : Presentation L (Fin 1) :=
  ⟨g.vertices-1,⟨(decodedGates L g hg).map (fun c => c.rename (split g.vertices hn))⟩⟩

theorem decode_code (g : Code) (hg : Valid L g) (hn : 0 < g.vertices) :
    presentationCode (decode L g hg hn) = g := by
  have hv : 1+(g.vertices-1)=g.vertices := by omega
  have hc : (presentationCode (decode L g hg hn)).constraints = g.constraints := by
    change ((decodedGates L g hg).map (fun c => c.rename (split g.vertices hn))).map constraintCode = _
    rw [List.map_map,←gateCode_decodedGates L g hg]
    apply List.map_congr_left
    intro c _
    unfold constraintCode gateCode Constraint.rename
    apply congrArg (Prod.mk c.symbol.val)
    apply congrArg List.ofFn
    funext i
    simp [split]
  cases g
  exact congrArg₂ Code.mk hv hc

variable [CommSemiring K] [Fintype D]

/-- Arbitrary weights on the retained boundary commute with the explicit
assignment bijection used by the canonical raw presentation encoding. -/
theorem weighted_partition_code {b : ℕ} (P : Presentation L (Fin b)) (w : (Fin b → D) → K) :
    (∑ σ : Fin (b+P.hidden) → D,
      w (fun i => σ (Fin.castAdd P.hidden i)) * eval L (presentationCode P) σ) =
        ∑ a, w a * P.table a := by
  let e : ((Fin b → D) × (Fin P.hidden → D)) ≃ (Fin (b+P.hidden) → D) :=
    (Equiv.sumArrowEquivProdArrow (Fin b) (Fin P.hidden) D).symm.trans
      (finSumFinEquiv.arrowCongr (Equiv.refl D))
  let f := fun σ : Fin (b+P.hidden) → D =>
    w (fun i => σ (Fin.castAdd P.hidden i)) * eval L (presentationCode P) σ
  have he (a : Fin b → D) (z : Fin P.hidden → D) :
      f (e (a,z)) = w a * P.inst.eval a z := by
    simp only [f,eval_presentationCode]
    dsimp [e]
    congr 1 <;> congr 1 <;> funext i <;> simp
  change (∑ σ, f σ) = _
  rw [←e.sum_comp f,Fintype.sum_prod_type]
  simp only [he,Presentation.table,Instance.partition,Finset.mul_sum]


/-- A fixed functional of the first variable, with a total empty-input default. -/
noncomputable def rootSum (w : (Fin 1 → D) → K) (g : Code) : K :=
  if hn : 0 < g.vertices then
    ∑ σ : Fin g.vertices → D, w (fun _ => σ ⟨0,hn⟩) * eval L g σ
  else 0

theorem rootSum_presentationCode (P : Presentation L (Fin 1)) (w : (Fin 1 → D) → K) :
    rootSum L w (presentationCode P) = ∑ a, w a * P.table a := by
  rw [rootSum,dif_pos (by change 0 < 1+P.hidden; omega)]
  convert weighted_partition_code L P w using 1
  apply Finset.sum_congr rfl
  intro σ _
  congr 2
  funext i
  rw [Fin.eq_zero i]
  rfl

theorem rootSum_decode (g : Code) (hg : Valid L g) (hn : 0 < g.vertices)
    (w : (Fin 1 → D) → K) :
    rootSum L w g = ∑ a, w a * (decode L g hg hn).table a := by
  rw [←rootSum_presentationCode,decode_code]

end ComplexCSP.RootedCSPCodePresentation
