import Counting.HolantUnified.FullDichotomy

/-!
Finite exact resources adjoined to a literal Holant language. The appended table
list keeps all original label numbers, so inclusion of original instances leaves
their independently defined graph serialization unchanged. The actual identity
TM2 therefore implements inclusion; no graph size or port information is erased.
-/
set_option backward.isDefEq.respectTransparency false

namespace Counting.HolantUnified.FiniteResources

open Paper2 Paper2.ExactInput Paper2.Problem Paper2.Tractable Paper2.Complexity
open scoped BigOperators

/-- Adjoin a fixed finite list of valid exact signature tables, retaining duplicates. -/
def extend (L R : Language) : Language :=
  ⟨L.val ++ R.val, by
    intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact L.property c hc
    · exact R.property c hc⟩

@[simp] theorem extend_count (L R : Language) :
    (extend L R).count = L.count + R.count := List.length_append

/-- Old labels occupy the prefix, with precisely the same numeric indices. -/
def baseLabel (L R : Language) (i : Fin L.count) : Fin (extend L R).count :=
  ⟨i.val, by rw [extend_count]; omega⟩

/-- Resource labels occupy the suffix; each occurrence still names a table. -/
def resourceLabel (L R : Language) (i : Fin R.count) : Fin (extend L R).count :=
  ⟨L.count + i.val, by rw [extend_count]; omega⟩

@[simp] theorem base_code (L R : Language) (i : Fin L.count) :
    (extend L R).code (baseLabel L R i) = L.code i := by
  change (L.val ++ R.val)[i.val]'(by exact (baseLabel L R i).isLt) = L.val[i.val]'i.isLt
  exact List.getElem_append_left i.isLt

@[simp] theorem resource_code (L R : Language) (i : Fin R.count) :
    (extend L R).code (resourceLabel L R i) = R.code i := by
  change (L.val ++ R.val)[L.count + i.val]'(by exact (resourceLabel L R i).isLt) = R.val[i.val]'i.isLt
  simpa only [Language.count, Nat.add_comm] using
    (List.getElem_append_right' L.val i.isLt).symm

/-- Transporting port indices changes no signature as a dependent pair. -/
private theorem signature_cast {m n : ℕ} (h : m = n)
    (f : Signature AlgebraicComplex n) :
    (⟨m, fun x => f (fun j => x (Fin.cast h.symm j))⟩ : AnySignature AlgebraicComplex) =
      ⟨n, f⟩ := by
  cases h
  rfl

private theorem family_entry (L : Language) (i : Fin L.count) :
    (⟨L.arity i.val, L.signature i⟩ : AnySignature AlgebraicComplex) =
      ⟨(L.code i).arity, (L.code i).denote (L.code_valid i)⟩ :=
  signature_cast (L.arity_index i) _

private theorem code_pair_eq {c d : SignatureCode} (h : c = d)
    (hc : c.Valid) (hd : d.Valid) :
    (⟨c.arity, c.denote hc⟩ : AnySignature AlgebraicComplex) = ⟨d.arity, d.denote hd⟩ := by
  cases h
  rfl

private theorem base_entry (L R : Language) (i : Fin L.count) :
    (⟨(extend L R).arity (baseLabel L R i).val,
      (extend L R).signature (baseLabel L R i)⟩ : AnySignature AlgebraicComplex) =
      ⟨L.arity i.val, L.signature i⟩ :=
  (family_entry _ _).trans ((code_pair_eq (base_code L R i) _ _).trans
    (family_entry L i).symm)

private theorem resource_entry (L R : Language) (i : Fin R.count) :
    (⟨(extend L R).arity (resourceLabel L R i).val,
      (extend L R).signature (resourceLabel L R i)⟩ : AnySignature AlgebraicComplex) =
      ⟨R.arity i.val, R.signature i⟩ :=
  (family_entry _ _).trans ((code_pair_eq (resource_code L R i) _ _).trans
    (family_entry R i).symm)

/-- The semantic language is exactly the union, with no implicit extra resource. -/
theorem extend_family (L R : Language) : (extend L R).family = L.family ∪ R.family := by
  ext f
  constructor
  · rintro ⟨i, rfl⟩
    by_cases hi : i.val < L.count
    · left
      refine ⟨⟨i.val, hi⟩, ?_⟩
      have he : i = baseLabel L R ⟨i.val, hi⟩ := Fin.ext rfl
      exact (base_entry L R ⟨i.val, hi⟩).symm.trans (congrArg
        (fun j => (⟨(extend L R).arity j.val, (extend L R).signature j⟩ :
          AnySignature AlgebraicComplex)) he.symm)
    · right
      have hir : i.val - L.count < R.count := by
        have hb : i.val < L.count + R.count := by simpa only [extend_count] using i.isLt
        omega
      refine ⟨⟨i.val - L.count, hir⟩, ?_⟩
      have he : i = resourceLabel L R ⟨i.val - L.count, hir⟩ := by
        apply Fin.ext
        simp only [resourceLabel]
        omega
      exact (resource_entry L R ⟨i.val - L.count, hir⟩).symm.trans (congrArg
        (fun j => (⟨(extend L R).arity j.val, (extend L R).signature j⟩ :
          AnySignature AlgebraicComplex)) he.symm)
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨baseLabel L R i, base_entry L R i⟩
    · exact ⟨resourceLabel L R i, resource_entry L R i⟩

@[simp] theorem base_arity (L R : Language) (i : Fin L.count) :
    (extend L R).arity i.val = L.arity i.val := by
  rw [← show (baseLabel L R i).val = i.val from rfl,
    Language.arity_index, base_code, ← Language.arity_index]
  rfl

/-- Every original graph validates unchanged against the extended language. -/
theorem extend_wellFormed (L R : Language) (G : Instance L) :
    G.val.WellFormed (extend L R).count 1 (extend L R).arity := by
  refine ⟨?_, G.property.2⟩
  intro v
  refine ⟨?_, ?_⟩
  · rw [extend_count]
    exact lt_of_lt_of_le (G.property.1 v).1 (Nat.le_add_right _ _)
  · rw [base_arity L R ⟨(G.val.vertices.get v).1, (G.property.1 v).1⟩]
    exact (G.property.1 v).2

/-- Include an original instance without modifying any raw record. -/
def includeBase (L R : Language) (G : Instance L) : Instance (extend L R) :=
  ⟨G.val, extend_wellFormed L R G⟩

@[simp] theorem includeBase_raw (L R : Language) (G : Instance L) :
    (includeBase L R G).val = G.val := rfl

/-- Exact byte equality uses both languages' existing validated graph encoders. -/
@[simp] theorem includeBase_bits (L R : Language) (G : Instance L) :
    (inputEncoding (extend L R)).encode (includeBase L R G) =
      (inputEncoding L).encode G := rfl

/-- The inclusion runs the already verified one-step finite identity machine. -/
noncomputable def includeBasePolyTime (L R : Language) :
    PolyTime (inputEncoding L) (inputEncoding (extend L R)) (includeBase L R) where
  tm := (identityPolyTime (inputEncoding L)).tm
  inputAlphabet := (identityPolyTime (inputEncoding L)).inputAlphabet
  outputAlphabet := (identityPolyTime (inputEncoding L)).outputAlphabet
  time := (identityPolyTime (inputEncoding L)).time
  outputsFun G := (identityPolyTime (inputEncoding L)).outputsFun G
  finiteAlphabets := (identityPolyTime (inputEncoding L)).finiteAlphabets

@[simp] theorem includeBase_time (L R : Language) :
    (includeBasePolyTime L R).time = 1 := rfl

private theorem denote_congr {c d : SignatureCode} (h : c = d)
    (hc : c.Valid) (hd : d.Valid) (x : Fin c.arity → Bool) (y : Fin d.arity → Bool)
    (hxy : ∀ i, x i = y (Fin.cast (congrArg SignatureCode.arity h) i)) :
    c.denote hc x = d.denote hd y := by
  cases h
  congr 1
  funext i
  exact hxy i

/-- The inclusion preserves the exact finite Holant sum for both edge kernels. -/
theorem includeBase_value (w : Wiring) (L R : Language) (G : Instance L) :
    value w (extend L R) (includeBase L R G) = value w L G := by
  unfold value Network.denote
  change (∑ z : (Fin G.val.edges.length × Bool) → Bool, _) =
    ∑ z : (Fin G.val.edges.length × Bool) → Bool, _
  apply Finset.sum_congr rfl
  intro z hz
  apply congrArg₂ (· * ·)
  · change (∏ v : Fin G.val.vertices.length, _) = ∏ v : Fin G.val.vertices.length, _
    apply Finset.prod_congr rfl
    intro v hv
    change (extend L R).signature (G.val.signatureLabel (extend_wellFormed L R G) v)
      (fun i => z (G.val.route (extend_wellFormed L R G) ⟨v, i⟩)) =
      L.signature (G.val.signatureLabel G.property v)
        (fun i => z (G.val.route G.property ⟨v, i⟩))
    unfold Language.signature
    have hc : (extend L R).code (G.val.signatureLabel (extend_wellFormed L R G) v) =
        L.code (G.val.signatureLabel G.property v) :=
      base_code L R (G.val.signatureLabel G.property v)
    apply denote_congr hc
    intro j
    apply congrArg z
    apply Prod.ext
    · apply Fin.ext
      rfl
    · rfl
  · rfl

/-- Restriction keeps the evaluator's finite machine and polynomial unchanged. -/
noncomputable def restrictPolyTime (L R : Language)
    {answer : Instance (extend L R) → RootCode}
    (m : PolyTime (inputEncoding (extend L R)) rootEncoding answer) :
    PolyTime (inputEncoding L) rootEncoding (fun G => answer (includeBase L R G)) where
  tm := m.tm
  inputAlphabet := m.inputAlphabet
  outputAlphabet := m.outputAlphabet
  time := m.time
  outputsFun G := m.outputsFun (includeBase L R G)
  finiteAlphabets := m.finiteAlphabets

/-- The actual extended-language evaluator also evaluates every original graph. -/
theorem inFP_of_extension (w : Wiring) (L R : Language)
    (h : Problem.InFP w (extend L R)) : Problem.InFP w L := by
  obtain ⟨answer, correct, ⟨m⟩⟩ := h
  refine ⟨(fun G => answer (includeBase L R G)), ?_, ⟨restrictPolyTime L R m⟩⟩
  intro G
  simpa only [includeBase_value] using correct (includeBase L R G)

/-- Restrict any correct bounded RootCode answer convention, without choosing
canonical isolating rectangles or changing the target output format. -/
def restrictAnswers (w : Wiring) (L R : Language) (a : BoundedAnswers w (extend L R)) :
    BoundedAnswers w L where
  answer G := a.answer (includeBase L R G)
  correct G := by simpa only [includeBase_value] using a.correct (includeBase L R G)
  outputBound := {
    bound := a.outputBound.bound
    length_le := fun G => a.outputBound.length_le (includeBase L R G) }

/-- One query on the unchanged graph bytes. Query validity, source query length
and target reply length are the original controlled-reflexivity certificates. -/
noncomputable def includeBaseReduction (w : Wiring) (L R : Language)
    (a : BoundedAnswers w (extend L R)) :
    LengthControlledOracleReduction (inputEncoding L) rootEncoding
      (inputEncoding (extend L R)) rootEncoding (restrictAnswers w L R a).answer a.answer := by
  let r := lengthControlled_refl (inputEncoding (extend L R)) rootEncoding a.answer a.outputBound
  exact {
    reduction := {
      machine := r.reduction.machine
      time := r.reduction.time
      correct := fun oracle h G => r.reduction.correct oracle h (includeBase L R G) }
    targetOutput := r.targetOutput
    queryBound := r.queryBound
    safeQuery := fun oracle h G t c run query =>
      r.safeQuery oracle h (includeBase L R G) t c run query }

/-- This is the basic oracle-machine bound; concrete inlining must still pay
for reading/writing replies using the retained target-output polynomial. -/
@[simp] theorem includeBaseReduction_time (w : Wiring) (L R : Language)
    (a : BoundedAnswers w (extend L R)) :
    (includeBaseReduction w L R a).reduction.time = 2 := rfl

@[simp] theorem includeBaseReduction_queryBound (w : Wiring) (L R : Language)
    (a : BoundedAnswers w (extend L R)) :
    (includeBaseReduction w L R a).queryBound = Polynomial.X := rfl

@[simp] theorem includeBaseReduction_outputBound (w : Wiring) (L R : Language)
    (a : BoundedAnswers w (extend L R)) :
    (includeBaseReduction w L R a).targetOutput.bound = a.outputBound.bound := rfl

/-- The fixed K basis acts on each family member, so finite adjunction also
commutes with the exact native-coordinate image used by the public theorem. -/
theorem extend_kImage (L R : Language) : kImage (extend L R) = kImage L ∪ kImage R := by
  simp only [kImage, extend_family, familyAction, Set.image_union]

/-- Closed classification of every explicitly adjoined finite resource list.
The ordinary and native graph problems retain D's strict RootCode answers and
its length-controlled hardness contract; the structural branches are disjoint. -/
theorem finite_resource_dichotomy (L R : Language) :
    ((Tract (L.family ∪ R.family) ∧ Problem.InFP .ordinary (extend L R)) ∨
      (¬Tract (L.family ∪ R.family) ∧ Problem.SharpPHard .ordinary (extend L R))) ∧
    ((Tract (kImage L ∪ kImage R) ∧ Problem.InFP .nativeX (extend L R)) ∨
      (¬Tract (kImage L ∪ kImage R) ∧ Problem.SharpPHard .nativeX (extend L R))) := by
  simpa only [extend_family, extend_kImage] using FullDichotomy.both_dichotomies (extend L R)

/-- The two fixed finite recognition machines halt on the actual concatenated
exact table list. No polynomial bound in varying table size is asserted. -/
theorem finite_resource_recognition :
    ∃ ordinary : TractRecognizer, ∃ native : NativeTractRecognizer,
      ∀ L R : Language,
        (∃ b : Bool, ∃ steps : ℕ,
          (fun c : Option ordinary.machine.tm.Cfg => c.bind ordinary.machine.tm.step)^[steps]
            (some (ordinary.initial (L.val ++ R.val))) = some (ordinary.final b) ∧
          ordinary.machine.tm.step (ordinary.final b) = none ∧
          (b = true ↔ Tract (L.family ∪ R.family))) ∧
        (∃ b : Bool, ∃ steps : ℕ,
          (fun c : Option native.machine.tm.Cfg => c.bind native.machine.tm.step)^[steps]
            (some (native.initial (L.val ++ R.val))) = some (native.final b) ∧
          native.machine.tm.step (native.final b) = none ∧
          (b = true ↔ Tract (kImage L ∪ kImage R))) := by
  obtain ⟨ordinary, native, ho, hn, _⟩ := FullDichotomy.main_theorem_with_native_recognition
  refine ⟨ordinary, native, ?_⟩
  intro L R
  constructor
  · obtain ⟨b, steps, run, halted, correct⟩ := ho (extend L R).val (extend L R).property
    refine ⟨b, steps, run, halted, ?_⟩
    change (b = true ↔ Tract (extend L R).family) at correct
    simpa only [extend_family] using correct
  · obtain ⟨b, steps, run, halted, correct⟩ := hn (extend L R).val (extend L R).property
    refine ⟨b, steps, run, halted, ?_⟩
    change (b = true ↔ Tract (kImage (extend L R))) at correct
    simpa only [extend_kImage] using correct

end Counting.HolantUnified.FiniteResources
