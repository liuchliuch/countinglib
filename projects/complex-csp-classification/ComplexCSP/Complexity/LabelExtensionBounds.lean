import ComplexCSP.Complexity.LabelExtension
import PlanarHom.BoundedIterationMachine

/-! # Explicit all-input polynomial bound for greedy extension states -/
namespace ComplexCSP.ComplexityLabelExtension
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open ComplexityWitnessPrimitives ComplexityTypeStackMachines MaltsevTypeStack ComplexityEncodingBounds
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)
variable (m : Fin d → Fin d → Fin d → Fin d) (space : Polynomial ℕ)

theorem choose_lt {p : State K d} {a : ℕ} (h : choose L basis m space p=some a) : a<d :=
  List.mem_range.mp (List.mem_of_mem_filter (List.mem_of_head? h))

theorem mem_replaceAt {xs : List ℕ} {i a b : ℕ} (h : b ∈ replaceAt xs i a) : b∈xs ∨ b=a := by
  obtain ⟨p,hp,hb⟩ := List.mem_map.mp h
  by_cases hi : p.2=i
  · exact Or.inr (by simpa [hi] using hb.symm)
  · exact Or.inl (by rw [←hb]; simpa [hi] using List.fst_mem_of_mem_zipIdx hp)

theorem step_invariants (p : State K d) :
    (step L basis m space p).1=p.1 ∧
    len (step L basis m space p) ≤ len p+1 ∧
    (target (step L basis m space p)).length=(target p).length ∧
    ∀a∈target (step L basis m space p), a∈target p ∨ a<d := by
  unfold step
  split
  · split
    · cases hc : choose L basis m space p with
      | none => simp +contextual [len,target]
      | some a =>
        refine ⟨rfl,le_rfl,replaceAt_length _ _ _,?_⟩
        intro b hb
        rcases mem_replaceAt hb with hb | rfl
        · exact Or.inl hb
        · exact Or.inr (choose_lt L basis m space hc)
    · simp +contextual [len,target]
  · simp +contextual [len,target]

theorem iterate_invariants (p : State K d) (i : ℕ) :
    ((step L basis m space)^[i] p).1=p.1 ∧
    len ((step L basis m space)^[i] p) ≤ len p+i ∧
    (target ((step L basis m space)^[i] p)).length=(target p).length ∧
    ∀a∈target ((step L basis m space)^[i] p), a∈target p ∨ a<d := by
  induction i with
  | zero => simp +contextual
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨hc,hn,ht,ha⟩ := step_invariants L basis m space ((step L basis m space)^[i] p)
    refine ⟨hc.trans ih.1,by omega,ht.trans ih.2.2.1,?_⟩
    intro a hmem
    rcases ha a hmem with hm | hd
    · exact ih.2.2.2 a hm
    · exact Or.inr hd

noncomputable def statePolynomial (d : ℕ) : Polynomial ℕ :=
  Polynomial.C 12*Polynomial.X^2 + Polynomial.C (12*d+30)*Polynomial.X+Polynomial.C 10

/-- The bound holds for every raw input, without a genuine-context promise.
Only the fixed color alphabet can enter a target word; lengths never grow. -/
theorem iterate_code_bound (count : ℕ) (p : State K d) (i : ℕ) (hi : i≤count) :
    ((stateCode basis).encode ((step L basis m space)^[i] p)).length ≤
      (statePolynomial d).eval ((BitEncoding.unaryNat.prod (stateCode basis)).encode (count,p)).length := by
  let N := ((BitEncoding.unaryNat.prod (stateCode (d:=d) basis)).encode (count,p)).length
  let out := (step L basis m space)^[i] p
  obtain ⟨hc,hn,ht,ha⟩ := iterate_invariants L basis m space p i
  have hN : N = 2*count + 2*(((ComplexityTypeStackConcrete.contextCode basis).prod
      (ComplexityCSPMarginalRowBounds.labelEncoding basis d)).encode p.1).length +
      2*len p + 2*(wordCode.encode (target p)).length+5 := by
    simp only [N,stateCode,BitEncoding.prod_length,BitEncoding.unaryNat_length,len,target,
      BitEncoding.bool,List.length_singleton]
    omega
  have hlength : (target p).length≤N := by
    have hl := BitEncoding.list_length_le BitEncoding.nat (target p)
    change (target p).length ≤ (wordCode.encode (target p)).length at hl
    omega
  have hb : ∀a∈target out,(BitEncoding.nat.encode a).length≤N+d := by
    intro a hamem
    rcases ha a hamem with hp | hd
    · have hh := encoded_mem_le BitEncoding.nat hp
      change (BitEncoding.nat.encode a).length ≤ (wordCode.encode (target p)).length at hh
      omega
    · exact (encodeNat_length_le a).trans (by omega)
  have hw := encoded_list_le BitEncoding.nat (target out) (N+d) hb
  rw [ht] at hw
  have hw' : (wordCode.encode (target out)).length≤(6*(N+d)+3)*N+1 :=
    hw.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hlength) _)
  have hn' : len out≤N := by dsimp only [out]; omega
  have hc' : (((ComplexityTypeStackConcrete.contextCode basis).prod
      (ComplexityCSPMarginalRowBounds.labelEncoding basis d)).encode out.1).length≤N := by
    dsimp only [out]
    rw [hc]
    omega
  have he : ((stateCode basis).encode out).length =
      2*(((ComplexityTypeStackConcrete.contextCode basis).prod
        (ComplexityCSPMarginalRowBounds.labelEncoding basis d)).encode out.1).length+
      2*len out+2*(wordCode.encode (target out)).length+4 := by
    simp only [stateCode,BitEncoding.prod_length,BitEncoding.unaryNat_length,len,target,
      BitEncoding.bool,List.length_singleton]
    omega
  change ((stateCode basis).encode out).length≤(statePolynomial d).eval N
  rw [he]
  simp only [statePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,
    Polynomial.eval_pow,Polynomial.eval_X]
  nlinarith

theorem fp_iterate : FP (BitEncoding.unaryNat.prod (stateCode (d:=d) basis)) (stateCode basis)
    (fun p => (step L basis m space)^[p.1] p.2) := by
  obtain ⟨body⟩ := fp_step L basis m space
  exact ⟨BoundedIterationMachine.computer (stateCode basis) (step L basis m space) body
    (statePolynomial d) (iterate_code_bound L basis m space)⟩

noncomputable def execute (p : ℕ × State K d) : Option (List ℕ) :=
  finish L m ((step L basis m space)^[p.1] p.2)

theorem fp_execute : FP (BitEncoding.unaryNat.prod (stateCode (d:=d) basis)) (optionCode wordCode)
    (execute L basis m space) := (fp_iterate L basis m space).comp (fp_finish L basis m)

/-- Run for the physically stored unary context dimension. Once a target is
complete or failure occurs, further steps leave it unchanged. -/
noncomputable def extend (p : State K d) : Option (List ℕ) :=
  execute L basis m space (ComplexityTypeStackConcrete.dimensionOf (context p),p)

theorem fp_extend : FP (stateCode (d:=d) basis) (optionCode wordCode) (extend L basis m space) :=
  ((((fp_context basis).comp (ComplexityTypeStackConcrete.fp_dimensionOf basis)).pair (fp_id _))).comp
    (fp_execute L basis m space)


/-- Public query shape used by seed, pinned-coordinate, and class-extension calls. -/
abbrev Query (K : Type) (d : ℕ) :=
  ComplexityTypeStackConcrete.Context K × (WeightedMaltsev.RowLabel K d × (ℕ × List ℕ))
noncomputable def queryCode : BitEncoding (Query K d) :=
  (ComplexityTypeStackConcrete.contextCode basis).prod
    ((ComplexityCSPMarginalRowBounds.labelEncoding basis d).prod (BitEncoding.unaryNat.prod wordCode))

def initial (q : Query K d) : State K d := ((q.1,q.2.1),q.2.2.1,q.2.2.2,true)

omit [DecidableEq K] in
theorem fp_initial : FP (queryCode (d:=d) basis) (stateCode basis) initial := by
  let ec := ComplexityTypeStackConcrete.contextCode basis
  let e := ComplexityCSPMarginalRowBounds.labelEncoding basis d
  have hc := fp_fst ec (e.prod (BitEncoding.unaryNat.prod wordCode))
  have hr := fp_snd ec (e.prod (BitEncoding.unaryNat.prod wordCode))
  have hw := hr.comp (fp_fst e (BitEncoding.unaryNat.prod wordCode))
  have hq := hr.comp (fp_snd e (BitEncoding.unaryNat.prod wordCode))
  exact (hc.pair hw).pair ((hq.comp (fp_fst BitEncoding.unaryNat wordCode)).pair
    ((hq.comp (fp_snd BitEncoding.unaryNat wordCode)).pair (fp_const _ BitEncoding.bool true)))

noncomputable def extendQuery (q : Query K d) : Option (List ℕ) :=
  extend L basis m space (initial q)

theorem fp_query : FP (queryCode (d:=d) basis) (optionCode wordCode) (extendQuery L basis m space) :=
  (fp_initial basis).comp (fp_extend L basis m space)

end ComplexCSP.ComplexityLabelExtension
