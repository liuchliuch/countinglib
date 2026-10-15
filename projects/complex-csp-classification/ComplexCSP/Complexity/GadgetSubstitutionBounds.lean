import ComplexCSP.Complexity.GadgetSubstitutionMachines

/-! # Bit-size bounds for the full raw gadget fold

The bound applies to every raw code, including malformed labels and arbitrarily
large binary port indices. It is therefore a genuine machine loop bound, not
merely a semantic valid-instance size estimate.
-/
namespace ComplexCSP.ComplexityGadgetSubstitution
open ComplexityCSPCode PlanarHom PlanarHom.Complexity ListFlattenMachines

private def natSize (v : ℕ) := (BitEncoding.nat.encode v).length
private def portsSize (ps : List ℕ) := (BitEncoding.nat.list.encode ps).length

private theorem getD_natSize (ps : List ℕ) (v : ℕ) : natSize (ps.getD v 0) ≤ portsSize ps := by
  rw [List.getD_eq_getElem?_getD,List.getD_getElem?]
  split_ifs with hv
  · have h := ListMapMachines.mem_le_sum_map natSize (List.getElem_mem hv)
    have hp := payloadSize_le_word BitEncoding.nat ps
    rw [payloadSize_eq] at hp
    change 2 * (ps.map natSize).sum + ps.length ≤ portsSize ps at hp
    omega
  · have h := encodeNat_length_le 0
    change natSize 0 ≤ 0 at h
    omega

private theorem remapVertex_size (t : Template) (offset : ℕ) (ps : List ℕ) (v : ℕ) :
    natSize (remapVertex t offset ps v) ≤ offset + portsSize ps + v := by
  unfold remapVertex
  split_ifs
  · exact (getD_natSize ps v).trans (by omega)
  · have h := encodeNat_length_le (offset + (v-t.boundary))
    change natSize (offset + (v-t.boundary)) ≤ offset + (v-t.boundary) at h
    omega

private theorem payloadSize_cons {A : Type} (e : BitEncoding A) (a : A) (as : List A) :
    payloadSize e (a::as) = 2*(e.encode a).length + 1 + payloadSize e as := by
  simp only [payloadSize_eq,List.map_cons,List.sum_cons,List.length_cons]
  omega

private def scopeCost (vs : List ℕ) := (vs.map (fun v => v+1)).sum
private def constraintCost (c : Gate) := c.1 + scopeCost c.2 + 1

private theorem remap_scope_payload (t : Template) (offset : ℕ) (ps vs : List ℕ) :
    payloadSize BitEncoding.nat (vs.map (remapVertex t offset ps)) ≤
      3 * scopeCost vs * (offset + portsSize ps + 1) := by
  induction vs with
  | nil => simp [payloadSize,BitEncoding.frames,scopeCost]
  | cons v vs ih =>
    have hv := remapVertex_size t offset ps v
    simp only [List.map_cons,payloadSize_cons,scopeCost,List.sum_cons] at *
    change 2*natSize (remapVertex t offset ps v)+1+_ ≤ _
    nlinarith

private theorem remapConstraint_size (t : Template) (offset : ℕ) (ps : List ℕ) (c : Gate) :
    (constraintEncoding.encode (remapConstraint t offset ps c)).length ≤
      12 * constraintCost c * (offset + portsSize ps + 1) := by
  have hp := remap_scope_payload t offset ps c.2
  have hw := word_length_le_payload BitEncoding.nat (c.2.map (remapVertex t offset ps))
  have hc := encodeNat_length_le c.1
  simp only [constraintEncoding,remapConstraint,BitEncoding.prod_length]
  dsimp only [constraintCost]
  nlinarith

private theorem remap_constraints_payload (t : Template) (offset : ℕ) (ps : List ℕ)
    (cs : List Gate) :
    payloadSize constraintEncoding (cs.map (remapConstraint t offset ps)) ≤
      25 * (cs.map constraintCost).sum * (offset + portsSize ps + 1) := by
  induction cs with
  | nil => simp [payloadSize,BitEncoding.frames]
  | cons c cs ih =>
    have hc := remapConstraint_size t offset ps c
    have hpos : 1 ≤ constraintCost c := by simp [constraintCost]
    simp only [List.map_cons,List.sum_cons,payloadSize_cons]
    nlinarith

/-- Explicit cost constant depending only on the fixed gadget descriptions. -/
def templateCost (t : Template) := t.privateCount + 25 * (t.constraints.map constraintCost).sum
def familyCost (ts : List Template) := (ts.map templateCost).sum
def contentSize (g : Code) := payloadSize constraintEncoding g.constraints

theorem attachTemplate_contentSize (t : Template) (g : Code) (ps : List ℕ) :
    contentSize (attachTemplate t g ps) ≤ contentSize g +
      templateCost t * (g.vertices + (BitEncoding.nat.list.encode ps).length + 1) := by
  have h := remap_constraints_payload t g.vertices ps t.constraints
  simp only [contentSize,attachTemplate,payloadSize_append]
  dsimp only [templateCost,portsSize] at *
  nlinarith

theorem gateTemplate_cost (ts : List Template) (a : Gate) :
    templateCost (gateTemplate ts a) ≤ familyCost ts := by
  by_cases h : a.1 < ts.length
  · exact ListMapMachines.mem_le_sum_map templateCost (gateTemplate_mem h)
  · simp [gateTemplate,List.getD_eq_getElem?_getD,h,templateCost,emptyTemplate]

theorem gateTemplate_privateCount (ts : List Template) (a : Gate) :
    (gateTemplate ts a).privateCount ≤ familyCost ts := by
  have h := gateTemplate_cost ts a
  unfold templateCost at h
  omega

theorem compileFrom_contentSize (ts : List Template) (g : Code) (as : List Gate)
    (V P : ℕ) (hv : g.vertices + as.length * familyCost ts ≤ V)
    (hp : ∀ a ∈ as, (BitEncoding.nat.list.encode a.2).length ≤ P) :
    contentSize (compileFrom ts g as) ≤
      contentSize g + as.length * familyCost ts * (V+P+1) := by
  induction as generalizing g with
  | nil => simp [compileFrom]
  | cons a as ih =>
    have ha := gateTemplate_privateCount ts a
    have ht := gateTemplate_cost ts a
    have hgV : g.vertices ≤ V := by omega
    have hport := hp a (by simp)
    have hs := attachTemplate_contentSize (gateTemplate ts a) g a.2
    have hm := Nat.mul_le_mul ht
      (show g.vertices + (BitEncoding.nat.list.encode a.2).length + 1 ≤ V+P+1 by omega)
    have hnext : (compileStep ts g a).vertices + as.length * familyCost ts ≤ V := by
      change g.vertices + (gateTemplate ts a).privateCount + as.length * familyCost ts ≤ V
      simp only [List.length_cons] at hv
      nlinarith
    have hi := ih (compileStep ts g a) hnext (fun b hb => hp b (by simp [hb]))
    change contentSize (compileFrom ts (compileStep ts g a) as) ≤ _
    change contentSize (compileStep ts g a) ≤ _ at hs
    simp only [List.length_cons]
    nlinarith

private theorem code_length (g : Code) :
    (encoding.encode g).length = 2*g.vertices + (constraintEncoding.list.encode g.constraints).length + 1 := by
  simp only [encoding,BitEncoding.retract,BitEncoding.prod_length,BitEncoding.unaryNat_length]

private theorem contentSize_le_length (g : Code) : contentSize g ≤ (encoding.encode g).length := by
  have h := payloadSize_le_word constraintEncoding g.constraints
  rw [code_length]
  unfold contentSize
  omega

private theorem code_length_le_contentSize (g : Code) :
    (encoding.encode g).length ≤ 2*g.vertices + 3*contentSize g + 2 := by
  have h := word_length_le_payload constraintEncoding g.constraints
  rw [code_length]
  unfold contentSize
  omega

/-- Explicit quadratic bound on every intermediate fold state for every raw
input. Unary vertex counts and framed binary port lengths are fully charged. -/
theorem compile_prefix_size_bound (ts : List Template) (g : Code) (as : List Gate) (i : ℕ) :
    (encoding.encode (compileFrom ts g (as.take i))).length ≤
      (Polynomial.C (20*(familyCost ts+1)^2)*(Polynomial.X+1)^2).eval
        ((encoding.prod constraintEncoding.list).encode (g,as)).length := by
  let N := ((encoding.prod constraintEncoding.list).encode (g,as)).length
  let C := familyCost ts
  have hN : N = 2*(encoding.encode g).length + (constraintEncoding.list.encode as).length+1 :=
    BitEncoding.prod_length _ _ _
  have hg : (encoding.encode g).length ≤ N := by omega
  have hv : g.vertices ≤ N := by have h := code_length g; omega
  have ha : as.length ≤ N := (BitEncoding.list_length_le constraintEncoding as).trans (by omega)
  have htake : (as.take i).length ≤ N := by rw [List.length_take]; omega
  have hp : ∀ a ∈ as.take i, (BitEncoding.nat.list.encode a.2).length ≤ N := by
    intro a hm
    have h := ListMapMachines.mem_le_sum_map (fun a => (constraintEncoding.encode a).length)
      (List.mem_of_mem_take hm)
    have hl := payloadSize_le_word constraintEncoding as
    rw [payloadSize_eq] at hl
    have he : (constraintEncoding.encode a).length = 2*(BitEncoding.nat.encode a.1).length +
        (BitEncoding.nat.list.encode a.2).length+1 := BitEncoding.prod_length _ _ _
    omega
  have hV : g.vertices + (as.take i).length*C ≤ N+N*C :=
    Nat.add_le_add hv (Nat.mul_le_mul_right C htake)
  have hcontent := compileFrom_contentSize ts g (as.take i) (N+N*C) N hV hp
  have hbase := (contentSize_le_length g).trans hg
  have hverts : (compileFrom ts g (as.take i)).vertices ≤ N+N*C := by
    rw [compileFrom_vertices]
    exact (Nat.add_le_add_left (ListMapMachines.sum_map_le_mul
      (fun a => (gateTemplate ts a).privateCount) (as.take i) C
      (fun a _ => gateTemplate_privateCount ts a)) g.vertices).trans hV
  have hout := code_length_le_contentSize (compileFrom ts g (as.take i))
  have hmul := Nat.mul_le_mul_right (C*(N+N*C+N+1)) htake
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_one]
  change _ ≤ 20*(C+1)^2*(N+1)^2
  change contentSize (compileFrom ts g (as.take i)) ≤
    contentSize g+(as.take i).length*C*(N+N*C+N+1) at hcontent
  nlinarith

/-- Actual polynomial-time TM2 compilation of the entire attachment fold. -/
theorem fp_compileFrom (ts : List Template) :
    FP (encoding.prod constraintEncoding.list) encoding (fun p => compileFrom ts p.1 p.2) :=
  ListFoldMachines.fp_foldl constraintEncoding encoding (compileStep ts) (fp_compileStep ts)
    (Polynomial.C (20*(familyCost ts+1)^2)*(Polynomial.X+1)^2)
    (fun g as i _ => compile_prefix_size_bound ts g as i)

/-- Actual polynomial-time raw compiler, preserving all original variables. -/
theorem fp_compile (ts : List Template) : FP encoding encoding (compile ts) := by
  have hbase : FP encoding encoding (fun g => Code.mk g.vertices []) :=
    (fp_vertices.pair (fp_const encoding constraintEncoding.list [])).transportOutput
      (fun _ => rfl)
  exact (hbase.pair fp_constraints).comp (fp_compileFrom ts)

end ComplexCSP.ComplexityGadgetSubstitution
