import ComplexCSP.Complexity.CSPCode
import PlanarHom.ListFlattenMachines

/-! # Uniform exact-output bounds for all prefix marginals

The auxiliary fixed language adds one unary delta predicate per color. A literal
prefix is imposed by actual unary constraints. Their partition identity is used
only for a semantic output-size bound, not as an exponential evaluation routine.
-/
namespace ComplexCSP.ComplexityCSPMarginalBounds
open scoped BigOperators
open ComplexityCSPCode PlanarHom PlanarHom.Complexity
variable {K : Type} {d s : ℕ} (L : Language (Fin d) K (Fin s))

private def pinArity (i : Fin (s+d)) : ℕ :=
  if h : i.val < s then L.arity ⟨i.val,h⟩ else 1

/-- Original symbols followed by the d unary delta-color predicates. -/
def pinLanguage [Zero K] [One K] : Language (Fin d) K (Fin (s+d)) where
  arity := pinArity L
  arity_pos i := by
    unfold pinArity
    split_ifs with h
    · exact L.arity_pos _
    · exact Nat.zero_lt_one
  value i := if h : i.val < s then
    fun a => L.value ⟨i.val,h⟩ (fun j => a ⟨j.val,by simpa only [pinArity,dif_pos h] using j.isLt⟩)
    else fun a => if a ⟨0,by simp [pinArity,h]⟩ = ⟨i.val-s,by omega⟩ then 1 else 0

/-- Prefix positions are consecutive original variable indices; no variable is
removed, so every isolated or unpinned variable remains summed. -/
def pinConstraints {k : ℕ} (a : Fin k → Fin d) : List (ℕ × List ℕ) :=
  List.ofFn (fun i => (s + (a i).val,[i.val]))

def pinCode (g : Code) {k : ℕ} (a : Fin k → Fin d) : Code :=
  ⟨g.vertices,g.constraints ++ pinConstraints (s:=s) a⟩

@[simp] theorem pinCode_vertices (g : Code) {k : ℕ} (a : Fin k → Fin d) :
    (pinCode (s:=s) g a).vertices = g.vertices := rfl

/-- Exact literal prefix predicate. -/
def Agrees (g : Code) {k : ℕ} (hk : k ≤ g.vertices) (a : Fin k → Fin d)
    (σ : Fin g.vertices → Fin d) : Prop := ∀ i, σ (Fin.castLE hk i) = a i

instance agreesDecidable (g : Code) {k : ℕ} (hk : k ≤ g.vertices)
    (a : Fin k → Fin d) (σ : Fin g.vertices → Fin d) : Decidable (Agrees g hk a σ) := by
  unfold Agrees
  infer_instance

def marginal [CommSemiring K] (g : Code) {k : ℕ} (hk : k ≤ g.vertices)
    (a : Fin k → Fin d) : K := ∑ σ, if Agrees g hk a σ then eval L g σ else 0

private theorem original_valid [Zero K] [One K] (g : Code) (c : ℕ × List ℕ)
    (hc : ConstraintValid L g.vertices c) : ConstraintValid (pinLanguage L) g.vertices c := by
  rcases hc with ⟨h,hlen,hvs⟩
  refine ⟨by omega,?_,hvs⟩
  simpa [pinLanguage,pinArity,h] using hlen

private theorem delta_valid [Zero K] [One K] (g : Code) {k : ℕ}
    (hk : k ≤ g.vertices) (a : Fin k → Fin d) (i : Fin k) :
    ConstraintValid (pinLanguage L) g.vertices (s+(a i).val,[i.val]) := by
  refine ⟨by have := (a i).isLt; omega,?_,?_⟩
  · simp [pinLanguage,pinArity]
  · intro v hv
    simp only [List.mem_singleton] at hv
    subst v
    exact lt_of_lt_of_le i.isLt hk

/-- Every compiled pin query is a valid original-plus-delta CSP instance. -/
theorem pinCode_valid [Zero K] [One K] (g : Code) (hg : Valid L g) {k : ℕ}
    (hk : k ≤ g.vertices) (a : Fin k → Fin d) :
    Valid (pinLanguage L) (pinCode (s:=s) g a) := by
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact original_valid L g c (hg c hc)
  · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hc
    exact delta_valid L g hk a i

private theorem original_value [CommSemiring K] (g : Code) (c : ℕ × List ℕ)
    (hc : ConstraintValid L g.vertices c) (σ : Fin g.vertices → Fin d) :
    entryValue (pinLanguage L) (constraintEntry (pinLanguage L) g σ c) =
      entryValue L (constraintEntry L g σ c) := by
  have hc' := original_valid L g c hc
  rw [constraintEntry, dif_pos hc', constraintEntry, dif_pos hc]
  dsimp only [entryValue, pinLanguage]
  rw [dif_pos hc.choose]
  congr 1

private theorem delta_value [CommSemiring K] (g : Code) {k : ℕ}
    (hk : k ≤ g.vertices) (a : Fin k → Fin d) (i : Fin k)
    (σ : Fin g.vertices → Fin d) :
    entryValue (pinLanguage L) (constraintEntry (pinLanguage L) g σ (s+(a i).val,[i.val])) =
      if σ (Fin.castLE hk i) = a i then 1 else 0 := by
  have hc := delta_valid L g hk a i
  rw [constraintEntry, dif_pos hc]
  dsimp only [entryValue, pinLanguage]
  rw [dif_neg (show ¬s+(a i).val < s by omega)]
  congr 1
  congr 1
  exact Fin.ext (Nat.add_sub_cancel_left s (a i).val)

/-- Actual added constraints give precisely the prefix indicator. -/
theorem pinCode_eval [CommSemiring K] (g : Code) (hg : Valid L g) {k : ℕ}
    (hk : k ≤ g.vertices) (a : Fin k → Fin d) (σ : Fin g.vertices → Fin d) :
    eval (pinLanguage L) (pinCode (s:=s) g a) σ =
      if Agrees g hk a σ then eval L g σ else 0 := by
  unfold eval assignmentWord
  simp only [List.map_map]
  change ((g.constraints ++ pinConstraints (s:=s) a).map
    (fun c => entryValue (pinLanguage L) (constraintEntry (pinLanguage L) g σ c))).prod = _
  rw [List.map_append,List.prod_append]
  have hbase : (g.constraints.map (fun c =>
      entryValue (pinLanguage L) (constraintEntry (pinLanguage L) g σ c))).prod = eval L g σ := by
    unfold eval assignmentWord
    rw [List.map_map]
    congr 1
    apply List.map_congr_left
    intro c hc
    exact original_value L g c (hg c hc) σ
  rw [hbase]
  simp only [pinConstraints,List.map_ofFn,List.prod_ofFn,Function.comp_def,delta_value L g hk a]
  rw [Fintype.prod_boole]
  by_cases h : ∀ i, σ (Fin.castLE hk i) = a i
  · simp [h,Agrees,eval,assignmentWord,List.map_map,Function.comp_def]
  · simp [h,Agrees]

/-- Literal pin-query partition equals the full partial-assignment marginal. -/
theorem pinCode_partition [CommSemiring K] (g : Code) (hg : Valid L g) {k : ℕ}
    (hk : k ≤ g.vertices) (a : Fin k → Fin d) :
    partition (pinLanguage L) (pinCode (s:=s) g a) = marginal L g hk a := by
  unfold partition marginal
  exact Finset.sum_congr rfl (fun σ _ => pinCode_eval L g hg hk a σ)

/-- No pins gives the original partition. -/
theorem marginal_empty [CommSemiring K] (g : Code) (a : Fin 0 → Fin d) :
    marginal L g (Nat.zero_le _) a = partition L g := by
  simp [marginal,Agrees,partition]

/-- Pinning every variable gives the literal assignment product. -/
theorem marginal_full [CommSemiring K] (g : Code) (a : Fin g.vertices → Fin d) :
    marginal L g le_rfl a = eval L g a := by
  have h (σ : Fin g.vertices → Fin d) : Agrees g le_rfl a σ ↔ σ = a := by
    exact funext_iff.symm
  simp only [marginal,h]
  simp

private theorem agrees_snoc (g : Code) {k : ℕ} (hk : k ≤ g.vertices)
    (hk1 : k+1 ≤ g.vertices) (a : Fin k → Fin d) (c : Fin d)
    (σ : Fin g.vertices → Fin d) :
    Agrees g hk1 (Fin.snoc a c) σ ↔
      Agrees g hk a σ ∧ σ ⟨k,by omega⟩ = c := by
  constructor
  · intro h
    constructor
    · intro i
      simpa only [Fin.snoc_castSucc,Fin.castLE,Fin.val_castSucc] using h i.castSucc
    · simpa only [Fin.snoc_last,Fin.castLE,Fin.val_last] using h (Fin.last k)
  · rintro ⟨ha,hc⟩ i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa only [Fin.snoc_last,Fin.castLE,Fin.val_last] using hc
    · simpa only [Fin.snoc_castSucc,Fin.castLE,Fin.val_castSucc] using ha j

/-- These are exactly the successive last-variable marginal layers, retaining
prefix order. In particular the uniform bound below applies to every layer. -/
theorem marginal_succ [CommSemiring K] (g : Code) {k : ℕ} (hk : k ≤ g.vertices)
    (hk1 : k+1 ≤ g.vertices) (a : Fin k → Fin d) :
    marginal L g hk a = ∑ c : Fin d, marginal L g hk1 (Fin.snoc a c) := by
  unfold marginal
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  simp_rw [agrees_snoc g hk hk1]
  by_cases h : Agrees g hk a σ
  · simp [h]
  · simp [h]

/-- Raw finite-word pin compiler; invalid words remain total syntax. -/
def rawPinCode (g : Code) (a : List ℕ) : Code :=
  ⟨g.vertices,g.constraints ++ List.ofFn (fun i : Fin a.length => (s+a.get i,[i.val]))⟩

def RawPrefixValid (g : Code) (a : List ℕ) : Prop :=
  a.length ≤ g.vertices ∧ ∀ c ∈ a, c < d

instance rawPrefixValidDecidable (g : Code) (a : List ℕ) :
    Decidable (RawPrefixValid (d:=d) g a) := by
  unfold RawPrefixValid
  infer_instance

def prefixColors (a : List ℕ) (ha : ∀ c ∈ a, c < d) : Fin a.length → Fin d :=
  fun i => ⟨a.get i,ha _ (List.get_mem a i)⟩

@[simp] theorem rawPinCode_eq (g : Code) (a : List ℕ) (ha : ∀ c ∈ a, c < d) :
    rawPinCode (s:=s) g a = pinCode (s:=s) g (prefixColors a ha) := rfl

theorem rawPinCode_valid [Zero K] [One K] (g : Code) (hg : Valid L g)
    (a : List ℕ) (ha : RawPrefixValid (d:=d) g a) :
    Valid (pinLanguage L) (rawPinCode (s:=s) g a) := by
  rw [rawPinCode_eq g a ha.2]
  exact pinCode_valid L g hg ha.1 _

theorem rawPinCode_partition [CommSemiring K] (g : Code) (hg : Valid L g)
    (a : List ℕ) (ha : RawPrefixValid (d:=d) g a) :
    partition (pinLanguage L) (rawPinCode (s:=s) g a) =
      marginal L g ha.1 (prefixColors a ha.2) := by
  rw [rawPinCode_eq g a ha.2]
  exact pinCode_partition L g hg ha.1 _

open ListFlattenMachines
private theorem code_length (g : Code) :
    (encoding.encode g).length = 2*g.vertices + (constraintEncoding.list.encode g.constraints).length + 1 := by
  simp only [encoding,BitEncoding.retract,BitEncoding.prod_length,BitEncoding.unaryNat_length]

private theorem delta_code_bound {k : ℕ} (a : Fin k → Fin d) (i : Fin k) (n : ℕ)
    (hk : k ≤ n) :
    (constraintEncoding.encode (s+(a i).val,[i.val])).length ≤ 2*(s+d) + 2*n + 5 := by
  have hs := encodeNat_length_le (s+(a i).val)
  have hi := encodeNat_length_le i.val
  have ha := (a i).isLt
  have hik := i.isLt
  simp only [constraintEncoding,BitEncoding.prod_length,BitEncoding.list,
    List.length_append,BitEncoding.frame_length,BitEncoding.frames_length,
    List.length_cons,List.length_nil,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
  change 2*(Computability.encodeNat (s+(a i).val)).length +
    (2*(Computability.encodeNat 1).length+1+(2*((Computability.encodeNat i.val).length+0)+1))+1 ≤ _
  change (Computability.encodeNat (s+(a i).val)).length ≤ s+(a i).val at hs
  change (Computability.encodeNat i.val).length ≤ i.val at hi
  rw [BinaryArithmetic.encodeNat_length] at hs hi
  norm_num
  omega

private theorem pin_payload_bound (g : Code) {k : ℕ} (hk : k ≤ g.vertices)
    (a : Fin k → Fin d) : payloadSize constraintEncoding (pinConstraints (s:=s) a) ≤
      k * (4*(s+d) + 4*g.vertices + 11) := by
  rw [payloadSize_eq]
  simp only [pinConstraints,List.map_ofFn,List.sum_ofFn,List.length_ofFn,Function.comp_def]
  have hsum : ∑ i : Fin k, (constraintEncoding.encode (s+(a i).val,[i.val])).length ≤
      k * (2*(s+d) + 2*g.vertices + 5) := by
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun i _ => delta_code_bound (s:=s) a i g.vertices hk)
  nlinarith

/-- One explicit quadratic covers every pinned query, uniformly in its prefix.
The original variable-count word is unary; scope indices and labels are charged. -/
theorem pinCode_length_bound (g : Code) {k : ℕ} (hk : k ≤ g.vertices)
    (a : Fin k → Fin d) :
    (encoding.encode (pinCode (s:=s) g a)).length ≤
      (Polynomial.C (20*(s+d+1)) * (Polynomial.X+1)^2).eval (encoding.encode g).length := by
  let N := (encoding.encode g).length
  have hN : g.vertices ≤ N := (Nat.le_add_right _ _).trans (size_le_encoding_length g)
  have hbase := payloadSize_le_word constraintEncoding g.constraints
  have hlen := code_length g
  have hp := pin_payload_bound (s:=s) g hk a
  have hw := word_length_le_payload constraintEncoding (g.constraints ++ pinConstraints (s:=s) a)
  rw [payloadSize_append] at hw
  rw [code_length]
  change 2*g.vertices + (constraintEncoding.list.encode
    (g.constraints ++ pinConstraints (s:=s) a)).length + 1 ≤ _
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one]
  change _ ≤ 20*(s+d+1)*(N+1)^2
  change N = _ at hlen
  have hkb : k * (4*(s+d)+4*g.vertices+11) ≤ N * (4*(s+d)+4*N+11) :=
    Nat.mul_le_mul (hk.trans hN) (by omega)
  have hDN : (s+d)*N ≤ (s+d)*(N+1)^2 :=
    Nat.mul_le_mul_left _ (by nlinarith)
  nlinarith

theorem rawPinCode_length_bound (g : Code) (a : List ℕ)
    (ha : RawPrefixValid (d:=d) g a) :
    (encoding.encode (rawPinCode (s:=s) g a)).length ≤
      (Polynomial.C (20*(s+d+1)) * (Polynomial.X+1)^2).eval (encoding.encode g).length := by
  rw [rawPinCode_eq g a ha.2]
  exact pinCode_length_bound g ha.1 _

section Field
variable [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

/-- One polynomial bounds every exact prefix-marginal output in the original
input length. The exponentially large sum is never run to establish this bound. -/
theorem exists_marginal_output_bound : ∃ p : Polynomial ℕ, ∀ (g : Code), Valid L g →
    ∀ (k : ℕ) (hk : k ≤ g.vertices) (a : Fin k → Fin d),
      ((numberFieldEncoding basis).encode (marginal L g hk a)).length ≤
        p.eval (encoding.encode g).length := by
  obtain ⟨p,hp⟩ := exists_partition_output_bound (pinLanguage L) basis
  refine ⟨p.comp (Polynomial.C (20*(s+d+1)) * (Polynomial.X+1)^2),?_⟩
  intro g hg k hk a
  rw [← pinCode_partition L g hg hk a]
  exact (hp (pinCode (s:=s) g a)).trans (by
    simpa only [Polynomial.eval_comp] using
      MachineComposition.natPolynomial_monotone p (pinCode_length_bound (s:=s) g hk a))
end Field
end ComplexCSP.ComplexityCSPMarginalBounds
