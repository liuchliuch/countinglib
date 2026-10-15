import ComplexCSP.Complexity.SupportPrefixSemantics
import ComplexCSP.Complexity.SupportFullCode
import ComplexCSP.Complexity.CSPValidation

/-! # Explicit safe preparation for eager support-compiler branches

FP.ite evaluates both supplied branches. These routines therefore normalize
scope/target inputs before calling a restricted-start machine. Every guard is an
actual finite/list bit machine, and all encoded promises are proved outputs of
these concrete preparations.
-/
namespace ComplexCSP.ComplexitySupportWitnessPrimitives
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding ComplexityWitnessPrimitives
open ComplexityProjectedClosure ComplexityCSPValidation
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.PairProjectionMachines
open PlanarHom.ArithmeticCircuitPrimitives
variable {d : ℕ}

def PositiveWitness (W : RawWitness) : Prop :=
  ∃ n : ℕ, 0 < n ∧ ∃ U : Code (Fin d) n, W = encodeCode U

noncomputable def positiveWitnessCode (d : ℕ) : BitEncoding {W : RawWitness // PositiveWitness (d:=d) W} :=
  witnessCode.restrict (PositiveWitness (d:=d))

def scopeValid (r : ℕ) (p : RawWitness × List ℕ) : Bool :=
  decide (p.2.length = r) && allBounded (p.1.1.length,p.2)

theorem fp_scopeValid (r : ℕ) : FP (witnessCode.prod wordCode) BitEncoding.bool (scopeValid r) := by
  have hW := fp_fst witnessCode wordCode
  have hn := (hW.comp (fp_fst tableCode maybeCode)).comp (ListCodecMachines.fp_length maybeCode.list)
  have hs := fp_snd witnessCode wordCode
  have hl := hs.comp (ListCodecMachines.fp_length BitEncoding.nat)
  have hlen := (hl.pair (fp_const (witnessCode.prod wordCode) BitEncoding.nat r)).comp NatListSumMachines.fp_equal
  have hb := (hn.pair hs).comp fp_allBounded
  exact (hlen.pair hb).comp (fp_bool_gate (fun p => p.1 && p.2))

def safeScope (r : ℕ) (p : RawWitness × List ℕ) : List ℕ :=
  if scopeValid r p then p.2 else List.replicate r 0

theorem fp_safeScope (r : ℕ) : FP (witnessCode.prod wordCode) wordCode (safeScope r) := by
  have ht : FP (witnessCode.prod wordCode) BitEncoding.bool (fun p => decide (scopeValid r p = true)) :=
    (fp_scopeValid r).congr (fun _ => by simp)
  exact ht.ite (fp_snd witnessCode wordCode)
    (fp_const (witnessCode.prod wordCode) wordCode (List.replicate r 0))

private theorem scope_realize {n r : ℕ} (xs : List ℕ) (hlen : xs.length=r)
    (hb : ∀ a ∈ xs, a<n) : ∃ ρ : Fin r → Fin n, scopeWord ρ = xs := by
  let ρ : Fin r → Fin n := fun i =>
    ⟨xs[i.val]'(by omega),hb _ (List.getElem_mem _)⟩
  refine ⟨ρ,?_⟩
  apply List.ext_getElem
  · simp [scopeWord,hlen]
  · intro i hi hi'
    simp [scopeWord,ρ]

theorem safeScope_realize {n r : ℕ} (W : Code (Fin d) n) (hn : 0<n) (xs : List ℕ) :
    ∃ ρ : Fin r → Fin n, safeScope r (encodeCode W,xs) = scopeWord ρ := by
  by_cases h : scopeValid r (encodeCode W,xs) = true
  · have hh : xs.length=r ∧ ∀ a∈xs, a<n := by
      simpa [scopeValid,allBounded,List.all_eq_true] using h
    obtain ⟨ρ,hρ⟩ := scope_realize xs hh.1 hh.2
    exact ⟨ρ,by simp [safeScope,h,hρ]⟩
  · refine ⟨fun _ => ⟨0,hn⟩,?_⟩
    simp [safeScope,h,scopeWord,List.ofFn_const]

theorem safeScope_actual {n r : ℕ} (W : Code (Fin d) n) (ρ : Fin r → Fin n) :
    safeScope r (encodeCode W,scopeWord ρ) = scopeWord ρ := by
  have h : scopeValid r (encodeCode W,scopeWord ρ) = true := by
    simp only [scopeValid,Bool.and_eq_true,decide_eq_true_eq,allBounded,List.all_eq_true,
      encodeCode_table_length]
    constructor
    · simp [scopeWord]
    · intro a ha
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
      exact (ρ i).isLt
  simp [safeScope,h]

def ScopeInputValid (r : ℕ) (p : RawWitness × List ℕ) : Prop :=
  ∃ n : ℕ, 0<n ∧ ∃ W : Code (Fin d) n, ∃ ρ : Fin r → Fin n,
    p.1=encodeCode W ∧ p.2=scopeWord ρ

noncomputable def validScopeInputCode (d r : ℕ) : BitEncoding {p : RawWitness × List ℕ // ScopeInputValid (d:=d) r p} :=
  (witnessCode.prod wordCode).restrict (ScopeInputValid (d:=d) r)

def prepareScope (r : ℕ) (p : {W : RawWitness // PositiveWitness (d:=d) W} × List ℕ) :
    {p : RawWitness × List ℕ // ScopeInputValid (d:=d) r p} :=
  ⟨(p.1.val,safeScope r (p.1.val,p.2)),by
    obtain ⟨n,hn,W,hW⟩ := p.1.property
    obtain ⟨ρ,hρ⟩ := safeScope_realize (r:=r) W hn p.2
    exact ⟨n,hn,W,ρ,hW,by simpa [hW] using hρ⟩⟩

theorem fp_prepareScope (r : ℕ) : FP ((positiveWitnessCode d).prod wordCode)
    (validScopeInputCode d r) (prepareScope r) := by
  have hv : FP (positiveWitnessCode d) witnessCode (fun p => p.val) := fp_code_view _ _ _ (fun _ => rfl)
  have hW := (fp_fst (positiveWitnessCode d) wordCode).comp hv
  have hs := fp_snd (positiveWitnessCode d) wordCode
  have hp := hW.pair hs
  exact (hW.pair (hp.comp (fp_safeScope r))).transportOutput (fun _ => rfl)

def targetValid (d : ℕ) (p : RawWitness × List ℕ) : Bool :=
  decide (p.2.length=p.1.1.length) && allBounded (d,p.2)

theorem fp_targetValid (d : ℕ) : FP (witnessCode.prod wordCode) BitEncoding.bool (targetValid d) := by
  have hW := fp_fst witnessCode wordCode
  have hn := (hW.comp (fp_fst tableCode maybeCode)).comp (ListCodecMachines.fp_length maybeCode.list)
  have ht := fp_snd witnessCode wordCode
  have hl := ht.comp (ListCodecMachines.fp_length BitEncoding.nat)
  have he := (hl.pair hn).comp NatListSumMachines.fp_equal
  have hb := ((fp_const (witnessCode.prod wordCode) BitEncoding.nat d).pair ht).comp fp_allBounded
  exact (he.pair hb).comp (fp_bool_gate (fun p => p.1 && p.2))

def safeTarget (d : ℕ) (p : RawWitness × List ℕ) : List ℕ :=
  if targetValid d p then p.2 else []

theorem fp_safeTarget (d : ℕ) : FP (witnessCode.prod wordCode) wordCode (safeTarget d) := by
  have ht : FP (witnessCode.prod wordCode) BitEncoding.bool (fun p => decide (targetValid d p=true)) :=
    (fp_targetValid d).congr (fun _ => by simp)
  exact ht.ite (fp_snd witnessCode wordCode) (fp_const (witnessCode.prod wordCode) wordCode [])

theorem safeTarget_bounded {n : ℕ} (W : Code (Fin d) n) (target : List ℕ) :
    (safeTarget d (encodeCode W,target)).length ≤ n ∧ ∀ a∈safeTarget d (encodeCode W,target), a<d := by
  by_cases h : targetValid d (encodeCode W,target)=true
  · have hh : target.length=n ∧ ∀ a∈target, a<d := by
      simpa [targetValid,allBounded,List.all_eq_true] using h
    simpa [safeTarget,h,hh.1] using And.intro hh.1.le hh.2
  · simp [safeTarget,h]

theorem safeTarget_actual {n : ℕ} (W : Code (Fin d) n) (target : Tuple (Fin d) n) :
    safeTarget d (encodeCode W,word target) = word target := by
  have h : targetValid d (encodeCode W,word target)=true := by
    simp only [targetValid,word_length,encodeCode_table_length,decide_true,Bool.true_and,
      allBounded,List.all_eq_true,decide_eq_true_eq]
    intro a ha
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp ha
    exact c.isLt
  simp [safeTarget,h]

def prepareSafePrefix (p : {W : RawWitness // PositiveWitness (d:=d) W} × (List ℕ × ℕ)) :
    {p : PrefixInput // PrefixInputValid d p} :=
  ⟨(p.1.val,safeTarget d (p.1.val,p.2.1),p.2.2),by
    obtain ⟨n,_,W,hW⟩ := p.1.property
    obtain ⟨hlen,hcol⟩ := safeTarget_bounded W p.2.1
    exact ⟨n,W,hW,by simpa [hW] using hlen,by simpa [hW] using hcol⟩⟩

theorem fp_prepareSafePrefix : FP ((positiveWitnessCode d).prod (wordCode.prod BitEncoding.nat))
    (validPrefixInputCode d) prepareSafePrefix := by
  have hv : FP (positiveWitnessCode d) witnessCode (fun p => p.val) := fp_code_view _ _ _ (fun _ => rfl)
  have hW := (fp_fst (positiveWitnessCode d) (wordCode.prod BitEncoding.nat)).comp hv
  have hp := fp_snd (positiveWitnessCode d) (wordCode.prod BitEncoding.nat)
  have ht := hp.comp (fp_fst wordCode BitEncoding.nat)
  have hk := hp.comp (fp_snd wordCode BitEncoding.nat)
  have htarget := (hW.pair ht).comp (fp_safeTarget d)
  exact (hW.pair (htarget.pair hk)).transportOutput (fun _ => rfl)

/-- A total safe caller of the restricted prefix machine on every target word.
Malformed target words use the empty prefix; both eager branches are safe. -/
theorem fp_safePrefixFrame (m : Fin d → Fin d → Fin d → Fin d) :
    FP ((positiveWitnessCode d).prod (wordCode.prod BitEncoding.nat)) rowsCode
      (fun p => prefixFrame d m (p.1.val,safeTarget d (p.1.val,p.2.1),p.2.2)) :=
  fp_prepareSafePrefix.comp (fp_prefixFrame d m)

end ComplexCSP.ComplexitySupportWitnessPrimitives
