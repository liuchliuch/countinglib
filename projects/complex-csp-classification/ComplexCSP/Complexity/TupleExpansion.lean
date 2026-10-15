import ComplexCSP.Complexity.CSPCode
import PlanarHom.ListFlattenMachines
import PlanarHom.ListDecompositionMachines
import PlanarHom.UnaryPolynomialMachines

/-! # Tuple-domain variables expanded into actual coordinate variables -/
namespace ComplexCSP.ComplexityTupleExpansion
open scoped BigOperators
open ComplexityCSPCode PlanarHom PlanarHom.Complexity
open PairProjectionMachines ArithmeticCircuitPrimitives BinaryArithmetic
variable {D K : Type} {s r : ℕ}

def language (L : Language (Fin r → D) K (Fin s)) (hr : 0 < r) : Language D K (Fin s) where
  arity i := L.arity i * r
  arity_pos i := Nat.mul_pos (L.arity_pos i) hr
  value i a := L.value i (fun j k => a (finProdFinEquiv (j,k)))

def ports (r v : ℕ) : List ℕ := (List.range r).map (fun k => v*r+k)
def compile (r : ℕ) (g : Code) : Code :=
  ⟨g.vertices*r, g.constraints.map (fun c => (c.1, c.2.flatMap (ports r)))⟩

@[simp] theorem vertices_compile (g : Code) : (compile r g).vertices = g.vertices*r := rfl
@[simp] theorem constraints_compile (g : Code) :
    (compile r g).constraints.length = g.constraints.length := by simp [compile]
@[simp] theorem ports_length (r v : ℕ) : (ports r v).length = r := by simp [ports]
@[simp] theorem flattened_length (ps : List ℕ) : (ps.flatMap (ports r)).length = ps.length*r := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp [List.flatMap_cons,ih,Nat.add_mul,Nat.add_comm]

theorem ports_lt {v n : ℕ} (hv : v<n) (w : ℕ) (hw : w ∈ ports r v) : w<n*r := by
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hw
  have hk : k<r := List.mem_range.mp hk
  nlinarith

theorem valid_compile (L : Language (Fin r → D) K (Fin s)) (hr : 0<r)
    (g : Code) (hg : Valid L g) : Valid (language L hr) (compile r g) := by
  intro c hc
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hc
  obtain ⟨hi,hlen,hv⟩ := hg a ha
  refine ⟨hi, ?_, ?_⟩
  · change (a.2.flatMap (ports r)).length = L.arity ⟨a.1,hi⟩ * r
    rw [flattened_length,hlen]
  · intro w hw
    obtain ⟨v,hv',hw⟩ := List.mem_flatMap.mp hw
    exact ports_lt (hv v hv') w hw

def assignments (n r : ℕ) : (Fin (n*r) → D) ≃ (Fin n → Fin r → D) :=
  (Equiv.arrowCongr finProdFinEquiv.symm (Equiv.refl D)).trans (Equiv.curry _ _ _)
@[simp] theorem assignments_apply (n r : ℕ) (a : Fin (n*r) → D) (i : Fin n) (j : Fin r) :
    assignments n r a i j = a (finProdFinEquiv (i,j)) := rfl

private theorem getElem_flattened (ps : List ℕ) (i : Fin ps.length) (j : Fin r) :
    (ps.flatMap (ports r))[i.val*r+j.val]'(by
      rw [flattened_length]
      simpa [finProdFinEquiv,Nat.add_comm,Nat.mul_comm] using (finProdFinEquiv (i,j)).isLt) =
      ps[i.val]*r+j.val := by
  induction ps with
  | nil => exact Fin.elim0 i
  | cons p ps ih =>
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [List.flatMap_cons,ports,List.getElem_append_left,j.isLt]
    · have hbound : (k.val+1)*r+j.val ≥ (ports r p).length := by simp; nlinarith
      simp only [List.flatMap_cons,Fin.val_succ,List.getElem_append_right hbound]
      have he : (k.val+1)*r+j.val-(ports r p).length = k.val*r+j.val := by
        simp only [ports_length,Nat.add_mul,Nat.one_mul]; omega
      simpa only [he,List.getElem_cons_succ] using ih k

theorem entry_compile [One K] (L : Language (Fin r → D) K (Fin s)) (hr : 0<r)
    (g : Code) (c : ℕ × List ℕ) (hc : ConstraintValid L g.vertices c)
    (a : Fin ((compile r g).vertices) → D) :
    entryValue (language L hr) (constraintEntry (language L hr) (compile r g) a
      (c.1,c.2.flatMap (ports r))) =
    entryValue L (constraintEntry L g (assignments g.vertices r a) c) := by
  have hc' : ConstraintValid (language L hr) (compile r g).vertices (c.1,c.2.flatMap (ports r)) := by
    obtain ⟨hi,hlen,hv⟩ := hc
    refine ⟨hi, by simp [language,hlen], ?_⟩
    intro w hw
    obtain ⟨v,hv',hw⟩ := List.mem_flatMap.mp hw
    exact ports_lt (hv v hv') w hw
  rw [constraintEntry,dif_pos hc',constraintEntry,dif_pos hc]
  simp only [entryValue,language,Function.comp_apply]
  congr 1
  funext i j
  congr 1
  apply Fin.ext
  have hi : i.val < c.2.length := by simpa only [hc.choose_spec.1] using i.isLt
  simpa only [scope,finProdFinEquiv,Equiv.symm_symm,Equiv.coe_fn_mk,assignments_apply,
    Nat.add_comm,Nat.mul_comm] using getElem_flattened c.2 ⟨i.val,hi⟩ j

theorem eval_compile [CommMonoid K] (L : Language (Fin r → D) K (Fin s)) (hr : 0<r)
    (g : Code) (hg : Valid L g) (a : Fin ((compile r g).vertices) → D) :
    eval (language L hr) (compile r g) a = eval L g (assignments g.vertices r a) := by
  simp only [eval,assignmentWord,compile,List.map_map,Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro c hc
  exact entry_compile L hr g c (hg c hc) a

theorem partition_compile [Fintype D] [CommSemiring K]
    (L : Language (Fin r → D) K (Fin s)) (hr : 0<r) (g : Code) (hg : Valid L g) :
    partition (language L hr) (compile r g) = partition L g := by
  simp only [partition,eval_compile L hr g hg]
  exact (assignments g.vertices r).sum_comp _

private theorem fp_fixed_map {A X Y : Type} (ex : BitEncoding X) (ey : BitEncoding Y)
    (xs : List A) (f : X → A → Y) (hf : ∀ a ∈ xs, FP ex ey (fun x => f x a)) :
    FP ex ey.list (fun x => xs.map (f x)) := by
  induction xs with
  | nil => exact fp_const _ _ []
  | cons a as ih =>
    exact ((hf a (by simp)).pair (ih (fun b hb => hf b (by simp [hb])))).comp
      (ListMutationMachines.fp_cons ey)

theorem fp_ports (r : ℕ) : FP BitEncoding.nat BitEncoding.nat.list (ports r) := by
  apply fp_fixed_map BitEncoding.nat BitEncoding.nat (List.range r)
  intro k hk
  have hm := ((fp_id BitEncoding.nat).pair (fp_const _ _ r)).comp fp_multiplication
  exact (hm.pair (fp_const _ _ k)).comp fp_addition

theorem fp_flattened_ports (r : ℕ) :
    FP BitEncoding.nat.list BitEncoding.nat.list (fun ps => ps.flatMap (ports r)) := by
  exact ((ListMapMachines.fp_map _ _ (ports r) (fp_ports r)).comp
    (ListFlattenMachines.fp_flatten BitEncoding.nat)).congr (fun ps => by
      change (ps.map (ports r)).flatten = ps.flatMap (ports r)
      induction ps with
      | nil => rfl
      | cons p ps ih => simp only [List.map_cons,List.flatten_cons,List.flatMap_cons,ih])

theorem fp_compile (r : ℕ) : FP encoding encoding (compile r) := by
  have hv : FP encoding (BitEncoding.unaryNat.prod constraintEncoding.list)
      (fun g => (g.vertices,g.constraints)) := fp_code_view _ _ _ (fun _ => rfl)
  have hn := hv.comp (fp_fst _ _)
  have hc := hv.comp (fp_snd _ _)
  have hnr := (hn.pair (fp_const encoding BitEncoding.unaryNat r)).comp UnaryPolynomialMachines.fp_mul
  have hgate : FP constraintEncoding constraintEncoding
      (fun c => (c.1,c.2.flatMap (ports r))) :=
    (fp_fst _ _).pair ((fp_snd _ _).comp (fp_flattened_ports r))
  have hcs := hc.comp (ListMapMachines.fp_map _ _ _ hgate)
  exact (hnr.pair hcs).transportOutput (fun _ => rfl)

end ComplexCSP.ComplexityTupleExpansion
