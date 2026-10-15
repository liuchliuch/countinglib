import ComplexCSP.Complexity.GadgetSubstitutionPresentation

/-! # Exact raw-code correctness of fixed-gadget substitution -/
namespace ComplexCSP.ComplexityGadgetSubstitution
open ComplexityCSPCode
open scoped BigOperators

variable {D K : Type} {s r : ℕ} {L : Language D K (Fin s)} {M : Language D K (Fin r)}

def templates (P : GadgetSubstitution.Gadgets L M) : List Template :=
  List.ofFn (fun j => presentationTemplate (P j))

def gateCode {n : ℕ} (c : Constraint M (Fin n)) : Gate :=
  (c.symbol.val, List.ofFn (fun i => (c.scope i).val))

@[simp] theorem gateTemplate_gateCode (P : GadgetSubstitution.Gadgets L M)
    {n : ℕ} (c : Constraint M (Fin n)) :
    gateTemplate (templates P) (gateCode c) = presentationTemplate (P c.symbol) := by
  unfold gateTemplate templates gateCode
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

/-- Typed left fold matching the raw compiler's consecutive fresh blocks. -/
def foldPresentations (P : GadgetSubstitution.Gadgets L M) {n : ℕ}
    (Q : Presentation L (Fin n)) (cs : List (Constraint M (Fin n))) : Presentation L (Fin n) :=
  cs.foldl (fun acc c => acc.mul ((P c.symbol).rename c.scope)) Q

theorem compileFrom_gateCodes (P : GadgetSubstitution.Gadgets L M) {n : ℕ}
    (Q : Presentation L (Fin n)) (cs : List (Constraint M (Fin n))) :
    compileFrom (templates P) (presentationCode Q) (cs.map gateCode) =
      presentationCode (foldPresentations P Q cs) := by
  induction cs generalizing Q with
  | nil => rfl
  | cons c cs ih =>
    change compileFrom (templates P)
      (compileStep (templates P) (presentationCode Q) (gateCode c)) (cs.map gateCode) = _
    simp only [compileStep]
    rw [gateTemplate_gateCode]
    change compileFrom (templates P)
      (attachTemplate (presentationTemplate (P c.symbol)) (presentationCode Q)
        (List.ofFn (fun i => (c.scope i).val))) (cs.map gateCode) = _
    rw [← presentationCode_mul_rename]
    exact ih _

theorem table_foldPresentations [CommSemiring K] [Fintype D]
    (P : GadgetSubstitution.Gadgets L M) (hP : GadgetSubstitution.Realizes P)
    {n : ℕ} (Q : Presentation L (Fin n)) (cs : List (Constraint M (Fin n))) (a : Fin n → D) :
    (foldPresentations P Q cs).table a = Q.table a * (cs.map (fun c => c.eval a)).prod := by
  induction cs generalizing Q with
  | nil => simp [foldPresentations]
  | cons c cs ih =>
    change (foldPresentations P (Q.mul ((P c.symbol).rename c.scope)) cs).table a = _
    rw [ih]
    simp only [Presentation.table_mul, Presentation.table_rename,
      List.map_cons, List.prod_cons, Constraint.eval, mul_assoc]
    rw [hP c.symbol (a ∘ c.scope)]

theorem degreeDivisible_foldPresentations
    (P : GadgetSubstitution.Gadgets L M) (δ : ℕ) (hP : ∀ j, (P j).DegreeDivisible δ)
    {n : ℕ} (Q : Presentation L (Fin n)) (hQ : Q.DegreeDivisible δ)
    (cs : List (Constraint M (Fin n))) : (foldPresentations P Q cs).DegreeDivisible δ := by
  induction cs generalizing Q with
  | nil => exact hQ
  | cons c cs ih => exact ih _ (hQ.mul ((hP c.symbol).rename c.scope))

/-- Decode each validated source row into its ordered typed constraint. -/
def decodedGates (M : Language D K (Fin r)) (g : Code) (hg : Valid M g) :
    List (Constraint M (Fin g.vertices)) :=
  g.constraints.attach.map (fun c =>
    ⟨⟨c.val.1,(hg c.val c.property).choose⟩, scope M g c.val (hg c.val c.property)⟩)

theorem gateCode_decodedGates (M : Language D K (Fin r)) (g : Code) (hg : Valid M g) :
    (decodedGates M g hg).map gateCode = g.constraints := by
  unfold decodedGates
  rw [List.map_map]
  calc
    _ = g.constraints.attach.map Subtype.val := by
      apply List.map_congr_left
      intro c _
      apply congrArg (Prod.mk c.val.1)
      apply List.ext_getElem
      · simp only [List.length_ofFn]
        exact (hg c.val c.property).choose_spec.1.symm
      · intro i hi hi'
        simp only [List.getElem_ofFn, scope]
    _ = _ := by simpa using (List.attach_map_val (l := g.constraints) (f := id))

theorem decodedGates_product [CommMonoid K] (M : Language D K (Fin r))
    (g : Code) (hg : Valid M g) (a : Fin g.vertices → D) :
    ((decodedGates M g hg).map (fun c => c.eval a)).prod = ComplexityCSPCode.eval M g a := by
  unfold decodedGates ComplexityCSPCode.eval assignmentWord
  rw [List.map_map]
  congr 1
  calc
    _ = g.constraints.attach.map (fun c => entryValue M (constraintEntry M g a c.val)) := by
      apply List.map_congr_left
      intro c _
      simp [constraintEntry, hg c.val c.property, entryValue, Constraint.eval]
    _ = _ := by
      simpa only [List.map_map, Function.comp_def] using
        (List.attach_map_val (l := g.constraints)
          (f := fun c => entryValue M (constraintEntry M g a c)))

/-- Literal equality of the raw output code and the encoding of the typed
fresh-copy compiler, rather than only a supplied semantic correspondence. -/
theorem compile_eq_presentationCode (P : GadgetSubstitution.Gadgets L M)
    (g : Code) (hg : Valid M g) :
    compile (templates P) g = presentationCode
      (foldPresentations P Presentation.one (decodedGates M g hg)) := by
  have he : (⟨g.vertices,[]⟩ : Code) =
      presentationCode (Presentation.one : Presentation L (Fin g.vertices)) := by
    simp [presentationCode,presentationTemplate,Template.code,Presentation.one]
  change compileFrom (templates P) ⟨g.vertices,[]⟩ g.constraints = _
  rw [he, ← gateCode_decodedGates M g hg]
  exact compileFrom_gateCodes P _ _

/-- Every compiled query is a valid literal base-language code. -/
theorem compile_valid (P : GadgetSubstitution.Gadgets L M) (g : Code) (hg : Valid M g) :
    Valid L (compile (templates P) g) := by
  rw [compile_eq_presentationCode P g hg]
  exact presentationCode_valid _

/-- Exact raw partition preservation for arbitrary finite scopes and repetitions. -/
theorem compile_partition [CommSemiring K] [Fintype D]
    (P : GadgetSubstitution.Gadgets L M) (hP : GadgetSubstitution.Realizes P)
    (g : Code) (hg : Valid M g) :
    ComplexityCSPCode.partition L (compile (templates P) g) = ComplexityCSPCode.partition M g := by
  rw [compile_eq_presentationCode P g hg, partition_presentationCode]
  simp only [table_foldPresentations P hP, Presentation.table_one, one_mul, decodedGates_product]
  rfl

/-- The raw output meets the actual occurrence-degree-divisibility promise. -/
theorem compile_degreeDivisible (P : GadgetSubstitution.Gadgets L M) (δ : ℕ)
    (hP : ∀ j, (P j).DegreeDivisible δ) (g : Code) (hg : Valid M g) :
    (toInstance L (compile (templates P) g) (compile_valid P g hg)).DegreeDivisible δ := by
  have htransport (out : Code) (ho : Valid L out)
      (he : out = presentationCode
        (foldPresentations P Presentation.one (decodedGates M g hg))) :
      (toInstance L out ho).DegreeDivisible δ := by
    subst out
    exact degreeDivisible_presentationCode _ δ
      (degreeDivisible_foldPresentations P δ hP Presentation.one
        (Presentation.degreeDivisible_one δ) _)
  exact htransport _ _ (compile_eq_presentationCode P g hg)

/-- Literal unweighted syntax size of a raw code, charging every occurrence. -/
def wireSize (g : Code) := g.vertices + g.constraints.length +
  (g.constraints.map (fun c => c.2.length)).sum

theorem wireSize_presentationCode {n : ℕ} (Q : Presentation L (Fin n)) :
    wireSize (presentationCode Q) = n + GadgetSubstitution.size Q := by
  simp [wireSize,presentationCode,presentationTemplate,Template.code,
    GadgetSubstitution.size,Instance.occurrences,constraintCode,List.length_flatMap,
    List.map_map,Function.comp_def,Nat.add_assoc]

theorem size_foldPresentations (P : GadgetSubstitution.Gadgets L M) {n : ℕ}
    (Q : Presentation L (Fin n)) (cs : List (Constraint M (Fin n))) :
    GadgetSubstitution.size (foldPresentations P Q cs) = GadgetSubstitution.size Q +
      (cs.map (fun c => GadgetSubstitution.size (P c.symbol))).sum := by
  induction cs generalizing Q with
  | nil => simp [foldPresentations]
  | cons c cs ih =>
    change GadgetSubstitution.size
      (foldPresentations P (Q.mul ((P c.symbol).rename c.scope)) cs) = _
    rw [ih]
    simp [Nat.add_assoc]

/-- Explicit linear bound for the very raw compiler used in the oracle query. -/
theorem wireSize_compile_le (P : GadgetSubstitution.Gadgets L M)
    (g : Code) (hg : Valid M g) :
    wireSize (compile (templates P) g) ≤
      g.vertices + GadgetSubstitution.gadgetBound P * g.constraints.length := by
  rw [compile_eq_presentationCode P g hg,wireSize_presentationCode,size_foldPresentations,
    GadgetSubstitution.size_one,zero_add]
  have hsum (cs : List (Constraint M (Fin g.vertices))) :
      (cs.map (fun c => GadgetSubstitution.size (P c.symbol))).sum ≤
        GadgetSubstitution.gadgetBound P * cs.length := by
    induction cs with
    | nil => simp
    | cons c cs ih =>
      have hc : GadgetSubstitution.size (P c.symbol) ≤ GadgetSubstitution.gadgetBound P :=
        Finset.single_le_sum (f := fun j => GadgetSubstitution.size (P j))
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ c.symbol)
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one]
      omega
  have hh := hsum (decodedGates M g hg)
  simpa only [decodedGates,List.length_map,List.length_attach] using Nat.add_le_add_left hh g.vertices

end ComplexCSP.ComplexityGadgetSubstitution
