import ComplexCSP.Complexity.CSPMarginalRowBounds
import ComplexCSP.Complexity.WitnessSizeBounds
import ComplexCSP.Complexity.MaltsevCacheBounds
import ComplexCSP.Structure.WeightedMaltsevMachineBridge

/-! # Uniform bounds for actual marginal class layers and search caches -/
namespace ComplexCSP.ComplexityCSPMarginalCacheBounds
open scoped BigOperators
open MaltsevRelations MaltsevWitness WeightedMaltsev
open ComplexityCSPMarginalBounds ComplexityCSPMarginalRowBounds
open ComplexityWitnessEncoding ComplexityWitnessPrimitives ComplexityWitnessSizeBounds
open ComplexityMaltsevCacheBounds ComplexityEncodingBounds
open PlanarHom PlanarHom.Complexity PlanarHom.MachineComposition
variable {K : Type} [Field K] [DecidableEq K] [Algebra ℚ K] {d s dimension : ℕ}
variable (L : Language (Fin d) K (Fin s)) (basis : Module.Basis (Fin dimension) ℚ K)

omit [Algebra ℚ K] in
/-- Every member of the proved label image is an actual normalized row. -/
theorem present_label_realized {k : ℕ} (G : (Fin (k+1) → Fin d) → K)
    (r : RowLabel K d) (hr : r ∈ presentLabels G) : ∃ a, tableLabel G a = r := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hr
  obtain ⟨_,a,ha⟩ := (BlockOrthogonalRowCount.mem_normalizedLabels _ _).mp hq
  refine ⟨a,?_⟩
  simp only [tableLabel,normalizedRow,view_ofFn,ha]

omit [Algebra ℚ K] in
theorem buildLayer_label_realized {k : ℕ} {m : Operation (Fin d)} (hm : IsMaltsev m)
    (W : MaltsevWitness.Code (Fin d) (k+1)) (G : (Fin (k+1) → Fin d) → K)
    (hW : Correct W {x | G x ≠ 0}) (hR : Preserves m (rowSupport G))
    (hTP : AllTypesPartition (rowSupport G) (fun x => tableLabel G (view x)))
    (evaluate : Tuple (Fin d) (k+1) → K) (he : ∀ x, evaluate x = G (view x))
    (defaultValue : Fin d) (entry : RowLabel K d × StoredCode d k)
    (hentry : entry ∈ buildLayer m W evaluate defaultValue) :
    ∃ a ∈ rowSupport G, tableLabel G a = entry.1 := by
  have hP : Correct (projectCode W k (Nat.le_succ k)) (rowSupport G) := by
    simpa only [projection_rowSupport] using projectCode_correct hW k (Nat.le_succ k)
  have hl := rowLabel_correct evaluate G he
  have ht : AllTypesPartition (rowSupport G) (rowLabel evaluate) := by rwa [hl]
  have hmemb : entry.1 ∈ (splitTypeClasses m (projectCode W k (Nat.le_succ k))
      (rowLabel evaluate) defaultValue).map Prod.fst := List.mem_map.mpr ⟨entry,hentry,rfl⟩
  obtain ⟨a,ha,hlabel⟩ := (splitTypeClasses_labels hm hR hP (rowLabel evaluate) ht defaultValue entry.1).mp hmemb
  exact ⟨a,ha,by simpa only [hl,view_ofFn] using hlabel⟩

omit [Algebra ℚ K] in
/-- BO proves the d-class bound for the actually computed layer. -/
theorem buildLayer_length_le {k : ℕ} {m : Operation (Fin d)} (hm : IsMaltsev m)
    (W : MaltsevWitness.Code (Fin d) (k+1)) (G : (Fin (k+1) → Fin d) → K)
    (hW : Correct W {x | G x ≠ 0}) (hR : Preserves m (rowSupport G))
    (hTP : AllTypesPartition (rowSupport G) (fun x => tableLabel G (view x)))
    (evaluate : Tuple (Fin d) (k+1) → K) (he : ∀ x, evaluate x = G (view x))
    (defaultValue : Fin d) (σ : K →+* ℂ)
    (hBO : BlockOrthogonality.BlockOrthogonal (fun x a => σ (tableRows G x a))) :
    (buildLayer m W evaluate defaultValue).length ≤ d := by
  have hP : Correct (projectCode W k (Nat.le_succ k)) (rowSupport G) := by
    simpa only [projection_rowSupport] using projectCode_correct hW k (Nat.le_succ k)
  have hl := rowLabel_correct evaluate G he
  have ht : AllTypesPartition (rowSupport G) (rowLabel evaluate) := by rwa [hl]
  have hlen := splitTypeClasses_length_le hm hR hP (rowLabel evaluate) ht defaultValue
    (presentLabels G) (by
      intro x hx
      simpa only [hl,view_ofFn] using tableLabel_mem_present G x hx)
  exact hlen.trans (presentLabels_card_le G σ hBO)

omit [Field K] [DecidableEq K] [Algebra ℚ K] in
private theorem labelAnchor_le (r : RowLabel K d) : labelAnchor r ≤ d := by
  cases r with
  | none => exact Nat.zero_le _
  | some p => exact p.1.isLt.le

omit [DecidableEq K] in
/-- Actual shared class records carry the bounded anchor/factor and literal
stored witness. This includes zero-dimensional present/absent witnesses. -/
theorem encodeClass_bound {k : ℕ} (entry : RowLabel K d × StoredCode d k) (B : ℕ)
    (hB : ((numberFieldEncoding basis).encode (labelFactor entry.1)).length ≤ B) :
    ((ComplexityWeightedLayers.classCode basis).encode (encodeClass entry)).length ≤
      2*d+2*B+(storedPolynomial d).eval k+2 := by
  have ha := (encodeNat_length_le (labelAnchor entry.1)).trans (labelAnchor_le entry.1)
  have hw := stored_code_bound entry.2
  simp only [ComplexityWeightedLayers.classCode,encodeClass,BitEncoding.prod_length]
  rw [BitEncoding.prod_length] at hw
  dsimp only at hw
  omega

omit [DecidableEq K] in
/-- The number of row classes is separately justified by the BO theorem below. -/
theorem encodeLayer_bound {k : ℕ} (layer : Layer K d k) (B : ℕ)
    (hlen : layer.length ≤ d)
    (hB : ∀ e ∈ layer, ((numberFieldEncoding basis).encode (labelFactor e.1)).length ≤ B) :
    ((ComplexityWeightedLayers.layerCode basis).encode (encodeLayer layer)).length ≤
      (6*(2*d+2*B+(storedPolynomial d).eval k+2)+3)*d+1 := by
  have h := encoded_list_le (ComplexityWeightedLayers.classCode basis) (encodeLayer layer)
    (2*d+2*B+(storedPolynomial d).eval k+2) (by
      intro e he
      obtain ⟨entry,hentry,rfl⟩ := List.mem_map.mp he
      exact encodeClass_bound basis entry B (hB entry hentry))
  simp only [encodeLayer,List.length_map] at h
  exact h.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hlen) 1)

/-- A single polynomial bounds every actually built marginal class layer.
All support/type/BO hypotheses are mathematical structural hypotheses, and the
field values/labels/witness data are the actual computed ones. -/
theorem exists_buildLayer_output_bound : ∃ p : Polynomial ℕ,
    ∀ (g : ComplexityCSPCode.Code), ComplexityCSPCode.Valid L g →
    ∀ (k : ℕ) (hk1 : k+1 ≤ g.vertices) (m : Operation (Fin d)), IsMaltsev m →
    ∀ (W : MaltsevWitness.Code (Fin d) (k+1)),
      Correct W {x | ComplexityCSPMarginalBounds.marginal L g hk1 x ≠ 0} →
      Preserves m (rowSupport (ComplexityCSPMarginalBounds.marginal L g hk1)) →
      AllTypesPartition (rowSupport (ComplexityCSPMarginalBounds.marginal L g hk1))
        (fun x => tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x)) →
    ∀ (evaluate : Tuple (Fin d) (k+1) → K),
      (∀ x, evaluate x = ComplexityCSPMarginalBounds.marginal L g hk1 (view x)) →
    ∀ (defaultValue : Fin d) (σ : K →+* ℂ),
      BlockOrthogonality.BlockOrthogonal (fun x a => σ (tableRows (ComplexityCSPMarginalBounds.marginal L g hk1) x a)) →
      ((ComplexityWeightedLayers.layerCode basis).encode
        (encodeLayer (buildLayer m W evaluate defaultValue))).length ≤
          p.eval (ComplexityCSPCode.encoding.encode g).length := by
  obtain ⟨p,hp⟩ := exists_normalized_marginal_bounds L basis
  refine ⟨(Polynomial.C 6*(Polynomial.C (2*d)+Polynomial.C 2*p+storedPolynomial d+2)+3)*
    Polynomial.C d+1,?_⟩
  intro g hg k hk1 m hm W hW hR hTP evaluate he defaultValue σ hBO
  let N := (ComplexityCSPCode.encoding.encode g).length
  have hkN : k ≤ N := by
    have h := ComplexityCSPCode.size_le_encoding_length g
    omega
  have hlen := buildLayer_length_le hm W _ hW hR hTP evaluate he defaultValue σ hBO
  have hfactor : ∀ e ∈ buildLayer m W evaluate defaultValue,
      ((numberFieldEncoding basis).encode (labelFactor e.1)).length ≤ p.eval N := by
    intro e hee
    obtain ⟨a,_,ha⟩ := buildLayer_label_realized hm W _ hW hR hTP evaluate he defaultValue e hee
    rw [← ha]
    exact (hp g hg k hk1 a).2
  have hb := encodeLayer_bound basis _ (p.eval N) hlen hfactor
  have hs := natPolynomial_monotone (storedPolynomial d) hkN
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_one,
    Polynomial.eval_ofNat]
  change _ ≤ (6*(2*d+2*p.eval N+(storedPolynomial d).eval N+2)+3)*d+1
  nlinarith

noncomputable def cacheEncoding : BitEncoding (List (ℕ × List (ComplexityRowNormalization.Result K d))) :=
  (BitEncoding.nat.prod (ComplexityRowNormalization.resultEncoding basis d).list).list

omit [DecidableEq K] in
/-- The shared cache translation preserves the literal encoding word. -/
theorem decodeTypeCache_encoding (cache : ListTypeCache (RowLabel K d)) :
    (cacheEncoding (d:=d) basis).encode (decodeTypeCache cache) =
      (BitEncoding.nat.prod (labelEncoding basis d).list).list.encode cache := by
  simp only [cacheEncoding,decodeTypeCache,BitEncoding.list,BitEncoding.prod,
    List.length_map,List.map_map,Function.comp_def,labelEncoding,BitEncoding.retract]

/-- The same original-input bound holds for every semantically valid separated
cache, including nonempty intermediate caches preserved by the search. No cache
cardinality, label-size, or encoded-length bound is assumed. -/
theorem exists_valid_cache_output_bound : ∃ p : Polynomial ℕ,
    ∀ (g : ComplexityCSPCode.Code), ComplexityCSPCode.Valid L g →
    ∀ (k : ℕ) (hk1 : k+1 ≤ g.vertices) (cache : ListTypeCache (RowLabel K d)),
      CacheValid (rowSupport (ComplexityCSPMarginalBounds.marginal L g hk1))
        (fun x => tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x)) (eraseTypeCache cache) →
      CacheSeparated (eraseTypeCache cache) → CacheListsNodup cache →
    ∀ (σ : K →+* ℂ),
      BlockOrthogonality.BlockOrthogonal (fun x a => σ (tableRows (ComplexityCSPMarginalBounds.marginal L g hk1) x a)) →
      ((cacheEncoding (d:=d) basis).encode (decodeTypeCache cache)).length ≤
        p.eval (ComplexityCSPCode.encoding.encode g).length := by
  obtain ⟨p,hp⟩ := exists_normalized_marginal_bounds L basis
  refine ⟨(Polynomial.C 6*(Polynomial.C 2*Polynomial.X+
      (Polynomial.C 6*p+3)*Polynomial.C d+2)+3)*((Polynomial.X+1)*Polynomial.C d)+1,?_⟩
  intro g hg k hk1 cache hv hs hn σ hBO
  let N := (ComplexityCSPCode.encoding.encode g).length
  let G := ComplexityCSPMarginalBounds.marginal L g hk1
  let label := fun x : Tuple (Fin d) k => tableLabel G (view x)
  let U := presentLabels G
  have hU : ∀ x ∈ rowSupport G, label (Vector.ofFn x) ∈ U := by
    intro x hx
    simpa only [label,view_ofFn] using tableLabel_mem_present G x hx
  have hB : ∀ r ∈ U, ((labelEncoding basis d).encode r).length ≤ p.eval N := by
    intro r hr
    obtain ⟨a,ha⟩ := present_label_realized G r hr
    rw [← ha]
    exact (hp g hg k hk1 a).1
  have hb := cache_bounds_of_invariants cache hv hs hn U hU
  have hsize := cache_code_bound (labelEncoding basis d) cache U (p.eval N) hB hb.1 hb.2
  have hcard : U.card ≤ d := presentLabels_card_le G σ hBO
  have hkN : k ≤ N := by
    have h := ComplexityCSPCode.size_le_encoding_length g
    omega
  rw [decodeTypeCache_encoding]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    Polynomial.eval_one,Polynomial.eval_ofNat]
  change _ ≤ (6*(2*N+(6*p.eval N+3)*d+2)+3)*((N+1)*d)+1
  apply hsize.trans
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul
  · exact Nat.add_le_add_right (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left _ hkN)
        (Nat.mul_le_mul_left _ hcard)) _)) _
  · exact Nat.mul_le_mul (Nat.add_le_add_right hkN 1) hcard

/-- Every runtime search cache at every marginal level has one original-input
polynomial bound. Its levels, duplicate-free label lists and number of entries
are all derived from the actual materialized search and BO's d-label bound. -/
theorem exists_typeCache_output_bound : ∃ p : Polynomial ℕ,
    ∀ (g : ComplexityCSPCode.Code), ComplexityCSPCode.Valid L g →
    ∀ (k : ℕ) (hk1 : k+1 ≤ g.vertices) (m : Operation (Fin d)), IsMaltsev m →
    ∀ (W : MaltsevWitness.Code (Fin d) k),
      Correct W (rowSupport (ComplexityCSPMarginalBounds.marginal L g hk1)) →
      Preserves m (rowSupport (ComplexityCSPMarginalBounds.marginal L g hk1)) →
      TypesPartition (rowSupport (ComplexityCSPMarginalBounds.marginal L g hk1))
        (fun x => tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x)) →
    ∀ (fuel len : ℕ), len+fuel=k → ∀ (target : Tuple (Fin d) k) (σ : K →+* ℂ),
      BlockOrthogonality.BlockOrthogonal (fun x a => σ (tableRows (ComplexityCSPMarginalBounds.marginal L g hk1) x a)) →
      ((cacheEncoding (d:=d) basis).encode (decodeTypeCache
        (materializedTypeSearch m W (fun x => tableLabel (ComplexityCSPMarginalBounds.marginal L g hk1) (view x))
          fuel len target []).2)).length ≤ p.eval (ComplexityCSPCode.encoding.encode g).length := by
  obtain ⟨p,hp⟩ := exists_normalized_marginal_bounds L basis
  refine ⟨(Polynomial.C 6*(Polynomial.C 2*Polynomial.X+
      (Polynomial.C 6*p+3)*Polynomial.C d+2)+3)*((Polynomial.X+1)*Polynomial.C d)+1,?_⟩
  intro g hg k hk1 m hm W hW hR hTP fuel len hdepth target σ hBO
  let N := (ComplexityCSPCode.encoding.encode g).length
  let G := ComplexityCSPMarginalBounds.marginal L g hk1
  let label := fun x : Tuple (Fin d) k => tableLabel G (view x)
  let cache := (materializedTypeSearch m W label fuel len target []).2
  let U := presentLabels G
  have hU : ∀ x ∈ rowSupport G, label (Vector.ofFn x) ∈ U := by
    intro x hx
    simpa only [label,view_ofFn] using tableLabel_mem_present G x hx
  have hB : ∀ r ∈ U, ((labelEncoding basis d).encode r).length ≤ p.eval N := by
    intro r hr
    obtain ⟨a,ha⟩ := present_label_realized G r hr
    rw [← ha]
    exact (hp g hg k hk1 a).1
  have hb := materialized_cache_bounds hm hR hW label hTP fuel len hdepth target U hU
  have hsize := cache_code_bound (labelEncoding basis d) cache U (p.eval N) hB hb.1 hb.2
  have hcard : U.card ≤ d := presentLabels_card_le G σ hBO
  have hkN : k ≤ N := by
    have h := ComplexityCSPCode.size_le_encoding_length g
    omega
  rw [decodeTypeCache_encoding]
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    Polynomial.eval_one,Polynomial.eval_ofNat]
  change _ ≤ (6*(2*N+(6*p.eval N+3)*d+2)+3)*((N+1)*d)+1
  apply hsize.trans
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul
  · exact Nat.add_le_add_right (Nat.mul_le_mul_left _
      (Nat.add_le_add_right (Nat.add_le_add (Nat.mul_le_mul_left _ hkN)
        (Nat.mul_le_mul_left _ hcard)) _)) _
  · exact Nat.mul_le_mul (Nat.add_le_add_right hkN 1) hcard

end ComplexCSP.ComplexityCSPMarginalCacheBounds
