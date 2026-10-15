import Paper2.DegreeCSP.QuarticLiftLayout
import Paper2.DegreeCSP.QuarticLiftInstanceOrdered
import Mathlib.Data.List.OfFn

/-! Exact indexed access to the ordered records emitted by the quartic-lift
compiler. These formulas identify every original, local, and edge clause. -/
namespace Paper2.DegreeCSP.QuarticLiftLayout
open Tractable QuarticLiftInstance
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem uniform_length {A : Type} {n t : ℕ} (f : Fin n → List A)
    (h : ∀ j,(f j).length=t) :
    ((List.finRange n).flatMap f).length=n*t := by
  rw [List.length_flatMap]
  simp_rw [h]
  simp

theorem uniform_get {A : Type} {n t : ℕ} (f : Fin n → List A)
    (h : ∀ j,(f j).length=t) (j : Fin n) (i : Fin t) :
    ((List.finRange n).flatMap f)[j.val*t+i.val]'(by
      rw [uniform_length f h]
      exact (Nat.add_lt_add_left i.isLt _).trans_le (by
        simpa only [Nat.succ_mul] using Nat.mul_le_mul_right t j.isLt)) =
      (f j)[i.val]'(by rw [h]; exact i.isLt) := by
  induction n with
  | zero => exact Fin.elim0 j
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simp only [List.finRange_succ,List.flatMap_cons,List.flatMap_map,Fin.val_zero,zero_mul,zero_add]
      rw [List.getElem_append_left (by rw [h]; exact i.isLt)]
    · simp only [List.finRange_succ,List.flatMap_cons,List.flatMap_map,Fin.val_succ]
      rw [List.getElem_append_right (by rw [h]; simp only [Nat.add_mul,Nat.one_mul]; omega)]
      have he : (j.val+1)*t+i.val-(f 0).length=j.val*t+i.val := by
        rw [h]; simp only [Nat.add_mul,Nat.one_mul]; omega
      simp only [he]
      exact ih (fun q => f q.succ) (fun q => h q.succ) j

theorem vertexFactors_length (P : Presentation AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (k label : ℕ) (x : Vertex) :
    (vertexFactors P labels k label x).length=P.constraints+2*k := by
  simp [vertexFactors,uniform_length (fun j : Fin 2 => List.replicate k (localFactor label x j))
    (fun _ => List.length_replicate)]

theorem factors_length (P : Presentation AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (k label : ℕ) (r : Input) :
    (factors P labels k label r).length=
      r.val.vertices.length*(P.constraints+2*k)+r.val.edges.length*k := by
  rw [factors,List.length_append,
    uniform_length _ (fun v => vertexFactors_length P labels k label ⟨r,v⟩),
    uniform_length _ (fun _ => List.length_replicate)]

def factorIndex (P : Presentation AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (k label : ℕ) (r : Input)
    (c : Tag P (Fin r.val.vertices.length) (Fin r.val.edges.length) k) :
    Fin (factors P labels k label r).length :=
  Fin.cast (factors_length P labels k label r).symm
    (constraintIndex P r.val.vertices.length r.val.edges.length k c)

theorem factors_get_old (P : Presentation AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (k label : ℕ) (r : Input)
    (v : Fin r.val.vertices.length) (c : Fin P.constraints) :
    (factors P labels k label r).get (factorIndex P labels k label r (Sum.inl (v,c))) =
      oldFactor P labels ⟨r,v⟩ c := by
  let old := (List.finRange r.val.vertices.length).flatMap
    (fun v => vertexFactors P labels k label ⟨r,v⟩)
  have hlen : old.length=r.val.vertices.length*(P.constraints+2*k) :=
    uniform_length _ (fun v => vertexFactors_length P labels k label ⟨r,v⟩)
  have hb : v.val*(P.constraints+2*k)+c.val<old.length := by
    rw [hlen]
    exact (Nat.add_lt_add_left (lt_of_lt_of_le c.isLt (Nat.le_add_right _ _)) _).trans_le
      (by simpa only [Nat.succ_mul] using Nat.mul_le_mul_right (P.constraints+2*k) v.isLt)
  simp only [List.get_eq_getElem,factorIndex,Fin.val_cast,constraintIndex_old_val]
  change (old ++ _)[v.val*(P.constraints+2*k)+c.val]'_ = _
  rw [List.getElem_append_left hb]
  rw [uniform_get _ (fun v => vertexFactors_length P labels k label ⟨r,v⟩)
    v (⟨c.val,lt_of_lt_of_le c.isLt (Nat.le_add_right _ _)⟩ : Fin (P.constraints+2*k))]
  simp only [vertexFactors]
  rw [List.getElem_append_left (by simpa using c.isLt)]
  simp

theorem factors_get_local (P : Presentation AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (k label : ℕ) (r : Input)
    (v : Fin r.val.vertices.length) (j : Fin 2) (q : Fin k) :
    (factors P labels k label r).get
      (factorIndex P labels k label r (Sum.inr (Sum.inl (v,j),q))) =
      localFactor label ⟨r,v⟩ j := by
  let old := (List.finRange r.val.vertices.length).flatMap
    (fun v => vertexFactors P labels k label ⟨r,v⟩)
  have hj : j.val*k+q.val<2*k :=
    (Nat.add_lt_add_left q.isLt _).trans_le
      (by simpa only [Nat.succ_mul] using Nat.mul_le_mul_right k j.isLt)
  have hi : P.constraints+j.val*k+q.val<P.constraints+2*k := by omega
  have hlen : old.length=r.val.vertices.length*(P.constraints+2*k) :=
    uniform_length _ (fun v => vertexFactors_length P labels k label ⟨r,v⟩)
  have hb : v.val*(P.constraints+2*k)+P.constraints+j.val*k+q.val<old.length := by
    rw [hlen]
    have hh : (v.val+1)*(P.constraints+2*k) ≤
        r.val.vertices.length*(P.constraints+2*k) := Nat.mul_le_mul_right _ v.isLt
    have hb' : v.val*(P.constraints+2*k)+(P.constraints+j.val*k+q.val)<
        (v.val+1)*(P.constraints+2*k) := by
      rw [Nat.add_mul,Nat.one_mul]
      exact Nat.add_lt_add_left hi _
    simpa only [Nat.add_assoc] using hb'.trans_le hh
  simp only [List.get_eq_getElem,factorIndex,Fin.val_cast,constraintIndex_local_val]
  change (old ++ _)[v.val*(P.constraints+2*k)+P.constraints+j.val*k+q.val]'_ = _
  rw [List.getElem_append_left hb]
  have he : v.val*(P.constraints+2*k)+P.constraints+j.val*k+q.val=
      v.val*(P.constraints+2*k)+(P.constraints+j.val*k+q.val) := by omega
  have hg := uniform_get (fun v => vertexFactors P labels k label ⟨r,v⟩)
    (fun v => vertexFactors_length P labels k label ⟨r,v⟩)
    v (⟨P.constraints+j.val*k+q.val,hi⟩ : Fin (P.constraints+2*k))
  have hg' : old[v.val*(P.constraints+2*k)+P.constraints+j.val*k+q.val]'hb =
      (vertexFactors P labels k label ⟨r,v⟩)[P.constraints+j.val*k+q.val]'(by
        rw [vertexFactors_length]; exact hi) := by
    simpa only [he] using hg
  rw [hg']
  simp only [vertexFactors]
  rw [List.getElem_append_right (by simp; omega)]
  simp only [List.length_ofFn]
  have he' : P.constraints+j.val*k+q.val-P.constraints=j.val*k+q.val := by omega
  simp only [he']
  rw [uniform_get _ (fun _ => List.length_replicate) j q]
  exact List.getElem_replicate _

theorem factors_get_outer (P : Presentation AlgebraicComplex (Fin 2))
    (labels : Fin P.constraints → ℕ) (k label : ℕ) (r : Input)
    (e : Fin r.val.edges.length) (q : Fin k) :
    (factors P labels k label r).get
      (factorIndex P labels k label r (Sum.inr (Sum.inr e,q))) =
      outerFactor label e.val := by
  let old := (List.finRange r.val.vertices.length).flatMap
    (fun v => vertexFactors P labels k label ⟨r,v⟩)
  have hlen : old.length=r.val.vertices.length*(P.constraints+2*k) :=
    uniform_length _ (fun v => vertexFactors_length P labels k label ⟨r,v⟩)
  simp only [List.get_eq_getElem,factorIndex,Fin.val_cast,constraintIndex_outer_val]
  change (old ++ _)[r.val.vertices.length*(P.constraints+2*k)+e.val*k+q.val]'_ = _
  rw [List.getElem_append_right (by rw [hlen]; omega)]
  simp only [hlen]
  have he : r.val.vertices.length*(P.constraints+2*k)+e.val*k+q.val-
      r.val.vertices.length*(P.constraints+2*k)=e.val*k+q.val := by omega
  simp only [he]
  rw [uniform_get _ (fun _ => List.length_replicate) e q]
  exact List.getElem_replicate _

end
end Paper2.DegreeCSP.QuarticLiftLayout
