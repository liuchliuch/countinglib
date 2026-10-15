import ComplexCSP.Structure.MaltsevTypeStackStoredBounds
import ComplexCSP.Complexity.TypeStackCodecs
import ComplexCSP.Complexity.WitnessSizeBounds

/-! # Literal bit bound for every materialized continuation state

The bound includes all unary prefix counters, target words, pending colors,
partial label lists, stack frames, and cache records. Label bit sizes come from
the independently proved fixed-field marginal bound, not an evaluator oracle.
-/
namespace ComplexCSP.MaltsevTypeStack
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding ComplexityWitnessPrimitives
open ComplexityTypeStackMachines ComplexityEncodingBounds ComplexityWitnessSizeBounds
open PlanarHom PlanarHom.Complexity
variable {A : Type} [DecidableEq A] {d n : ℕ}

def wordBound (d n : ℕ) : ℕ := (6*d+3)*n+1
def labelListBound (r B : ℕ) : ℕ := (6*B+3)*r+1
def frameBound (d n r B : ℕ) : ℕ :=
  2*n + 2*wordBound d n + 2*wordBound d d + labelListBound r B + 3
def cacheEntryBound (n r B : ℕ) : ℕ := 2*n + labelListBound r B + 1
/-- An explicit multivariate polynomial, with no semantic size argument hidden
inside the definition. -/
def stateBound (d n r B k : ℕ) : ℕ :=
  2*n + 2*wordBound d n + 2*labelListBound r B +
  2*((6*frameBound d n r B+3)*n+1) +
  ((6*cacheEntryBound n r B+3)*k+1) + 7

omit [DecidableEq A] in
theorem WordValid.code_bound {xs : List ℕ} (h : WordValid d n xs) :
    (wordCode.encode xs).length ≤ wordBound d n := by
  obtain ⟨x,rfl⟩ := h
  simpa [tuplePolynomial,wordBound] using word_code_bound x

omit [DecidableEq A] in
theorem pending_code_bound {xs : List ℕ} (h : xs.Sublist (List.range d)) :
    (wordCode.encode xs).length ≤ wordBound d d := by
  have hb := encoded_list_le BitEncoding.nat xs d (by
    intro a ha
    exact (encodeNat_length_le a).trans (List.mem_range.mp (h.subset ha)).le)
  have hl : xs.length ≤ d := by simpa using h.length_le
  exact hb.trans (by unfold wordBound; gcongr)

theorem LabelList.code_bound (e : BitEncoding A) {U : Finset A} {xs : List A}
    (h : LabelList U xs) (B : ℕ) (hB : ∀ a ∈ U, (e.encode a).length ≤ B) :
    (e.list.encode xs).length ≤ labelListBound U.card B := by
  have hb := encoded_list_le e xs B (fun a ha => hB a (h.2 a ha))
  exact hb.trans (by unfold labelListBound; gcongr; exact h.length_le)

omit [DecidableEq A] in
theorem frame_code_bound (e : BitEncoding A) (f : Frame A) (r B : ℕ)
    (hlen : f.parentLen ≤ n) (ht : WordValid d n f.parentTarget)
    (hcolors : f.remainingColors.Sublist (List.range d))
    (hlabels : (e.list.encode f.accumulatedLabels).length ≤ labelListBound r B) :
    ((frameCode e).encode f).length ≤ frameBound d n r B := by
  have hw := ht.code_bound
  have hc := pending_code_bound hcolors
  simp only [frameCode,BitEncoding.retract,frameViewCode,frameView,BitEncoding.prod_length,
    BitEncoding.unaryNat_length]
  unfold frameBound
  omega

/-- State-code bound from the proved logical invariant and concrete label code
lengths. The cache-record count k is explicit and can be the transition budget. -/
theorem stateValid_code_bound (e : BitEncoding A) {U : Finset A} {s : State A}
    (hs : StateValid d n U s) (B k : ℕ)
    (hB : ∀ a ∈ U, (e.encode a).length ≤ B) (hk : s.cache.length ≤ k) :
    ((stateCode e).encode s).length ≤ stateBound d n U.card B k := by
  have hw := hs.2.1.1.code_bound
  have hr := hs.2.2.1.1.code_bound e B hB
  have hf : ∀ f ∈ s.stack, ((frameCode e).encode f).length ≤ frameBound d n U.card B := by
    intro f hmem
    exact frame_code_bound e f U.card B ((hs.1.2.mem_lt hmem).le.trans hs.1.1)
      (hs.2.1.2 f hmem).1 (hs.2.1.2 f hmem).2 ((hs.2.2.1.2.1 f hmem).code_bound e B hB)
  have hstack := encoded_list_le (frameCode e) s.stack (frameBound d n U.card B) hf
  have hsl : s.stack.length ≤ n := hs.1.stack_length
  have hstack' : (((frameCode e).list).encode s.stack).length ≤ (6*frameBound d n U.card B+3)*n+1 :=
    hstack.trans (by gcongr)
  have hc : ∀ x ∈ s.cache,
      ((BitEncoding.nat.prod e.list).encode x).length ≤ cacheEntryBound n U.card B := by
    intro x hx
    have hxlen := (encodeNat_length_le x.1).trans (hs.2.2.2 x hx)
    have hxlabels := (hs.2.2.1.2.2 x hx).code_bound e B hB
    simp only [BitEncoding.prod_length]
    unfold cacheEntryBound
    omega
  have hcache := encoded_list_le (BitEncoding.nat.prod e.list) s.cache (cacheEntryBound n U.card B) hc
  have hcache' : ((ComplexityTypeCache.cacheEncoding e).encode s.cache).length ≤
      (6*cacheEntryBound n U.card B+3)*k+1 := hcache.trans (by gcongr)
  have hb : (BitEncoding.bool.encode s.returning).length = 1 := by cases s.returning <;> rfl
  simp only [stateCode,BitEncoding.retract,stateViewCode,stateView,BitEncoding.prod_length,
    BitEncoding.unaryNat_length]
  change 2*(BitEncoding.bool.encode s.returning).length +
    (2*s.currentLen + (2*(wordCode.encode s.currentTarget).length +
      (2*(e.list.encode s.returnedLabels).length +
        (2*((frameCode e).list.encode s.stack).length +
          ((ComplexityTypeCache.cacheEncoding e).encode s.cache).length + 1) + 1) + 1) + 1) + 1 ≤ _
  rw [hb]
  unfold stateBound
  have hlen := hs.1.1
  omega

/-- Every genuinely reached state has this literal bit bound. The only bound on
label bit sizes is on the actual present-label set, justified for marginals by
the independent number-field output theorem. -/
theorem stored_reached_code_bound (e : BitEncoding A)
    {m : Operation (Fin d)} {W : StoredCode d n} {R : Set (Fin n → Fin d)}
    (hR : Preserves m R) (hW : Correct W.toCode R)
    (label : Tuple (Fin d) n → A) (labelRaw : List ℕ → A)
    (hlab : ∀ x, labelRaw (word x) = label x)
    (U : Finset A) (hU : ∀ x ∈ R, label (Vector.ofFn x) ∈ U)
    (B : ℕ) (hB : ∀ a ∈ U, (e.encode a).length ≤ B)
    (len : ℕ) (hlen : len ≤ n) (target : Tuple (Fin d) n)
    {s : State A} {k : ℕ}
    (hr : Runs (step n (List.range d) (storedReconstruct m W) labelRaw)
      (callState len (word target) [] []) s k) :
    ((stateCode e).encode s).length ≤ stateBound d n U.card B k := by
  obtain ⟨hv,hk⟩ := stored_reached_sizes hR hW label labelRaw hlab U hU len hlen target hr
  exact stateValid_code_bound e hv B k hB hk

omit [DecidableEq A] in
theorem stateBound_mono {d n n' r r' B B' k k' : ℕ}
    (hn : n ≤ n') (hr : r ≤ r') (hB : B ≤ B') (hk : k ≤ k') :
    stateBound d n r B k ≤ stateBound d n' r' B' k' := by
  unfold stateBound frameBound cacheEntryBound wordBound labelListBound
  gcongr

/-- A one-variable cap polynomial after substituting the proved class bound d,
the original-instance label polynomial, and the actual transition budget. -/
noncomputable def statePolynomial (d : ℕ) (labelPolynomial : Polynomial ℕ) : Polynomial ℕ :=
  let w := Polynomial.C (6*d+3) * Polynomial.X + 1
  let labels := (6*labelPolynomial+3)*Polynomial.C d+1
  let frame := 2*Polynomial.X + 2*w + Polynomial.C (2*wordBound d d) + labels + 3
  let entry := 2*Polynomial.X + labels + 1
  let budget := 2*(1+Polynomial.C d*((Polynomial.X+1)*Polynomial.C d))
  2*Polynomial.X + 2*w + 2*labels + 2*((6*frame+3)*Polynomial.X+1) +
    ((6*entry+3)*budget+1)+7

omit [DecidableEq A] in
@[simp] theorem statePolynomial_eval (d : ℕ) (p : Polynomial ℕ) (N : ℕ) :
    (statePolynomial d p).eval N = stateBound d N d (p.eval N) (2*(1+d*((N+1)*d))) := by
  simp [statePolynomial,stateBound,frameBound,cacheEntryBound,wordBound,labelListBound]

end ComplexCSP.MaltsevTypeStack
