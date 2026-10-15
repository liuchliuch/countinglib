import Paper2.DegreeCSP.SemanticCompiler
import Paper2.DegreeCSP.EqualityMultiples

/-! A degree-k Boolean CSP with literal disequality constraints compiles to
an actual native-X network over the original language and one literal Eq_k.
Every ordered scope occurrence is retained by the incidence compiler. -/
namespace Paper2.DegreeCSP
open Paper2.Tractable Paper2.ExactInput
noncomputable section
set_option backward.isDefEq.respectTransparency false

def disequalityTable : Signature AlgebraicComplex 2 :=
  fun x => Signature.disequality (x 0) (x 1)

def sourceFamily (F : SignatureFamily AlgebraicComplex) :
    SignatureFamily AlgebraicComplex := insert ⟨2,disequalityTable⟩ F

def targetFamily (F : SignatureFamily AlgebraicComplex) (k : ℕ) :
    SignatureFamily AlgebraicComplex := insert ⟨k,equality k⟩ F

theorem member_realizable {K : Type} [CommSemiring K]
    (F : SignatureFamily K) {n : ℕ} (f : Signature K n)
    (hf : (⟨n,f⟩ : AnySignature K) ∈ F) : NetworkRealizable F f := by
  refine ⟨n,Network.corolla f,Equiv.refl _,?_,?_,?_⟩
  · intro v
    exact hf
  · intro e
    exact Fin.elim0 e
  · simpa only [Tensor.reindex_refl] using Network.denote_corolla f

theorem fixed_equality_realizable (F : SignatureFamily AlgebraicComplex) (k : ℕ) :
    NetworkRealizable (targetFamily F k) (equality k) := by
  apply member_realizable
  exact Set.mem_insert _ _

theorem signature_congr_realizable {K : Type} [CommSemiring K]
    {F : SignatureFamily K} {n m : ℕ} {f : Signature K n} {g : Signature K m}
    (he : (⟨n,f⟩ : AnySignature K) = ⟨m,g⟩) (hg : NetworkRealizable F g) :
    NetworkRealizable F f := by
  cases he
  exact hg

namespace Instance
variable (I : Instance AlgebraicComplex)

theorem native_vertex_realizable (F : SignatureFamily AlgebraicComplex)
    (k : ℕ) (hk : 3 ≤ k) (hu : I.Uses (sourceFamily F))
    (hd : I.DegreeDivisible k) (v : I.IncidenceVertex) :
    NetworkRealizable (targetFamily F k) (I.incidence.vertex v) := by
  cases v with
  | inl c =>
    have hc := hu c
    rcases Set.mem_insert_iff.mp hc with hc | hc
    · change NetworkRealizable _ (I.table c)
      exact signature_congr_realizable hc
        (disequality_realizable _ k hk (fixed_equality_realizable F k))
    · apply member_realizable
      exact Set.mem_insert_of_mem _ hc
  | inr v =>
    obtain ⟨m,hm⟩ := hd v
    have hn : I.degree v = m*k := by simpa only [Nat.mul_comm] using hm
    change NetworkRealizable _ (equality (I.degree v))
    rw [hn]
    exact equality_multiple_realizable _ k hk (fixed_equality_realizable F k) m

def nativeReplacement (F : SignatureFamily AlgebraicComplex)
    (k : ℕ) (hk : 3 ≤ k) (hu : I.Uses (sourceFamily F))
    (hd : I.DegreeDivisible k) : I.Replacement (targetFamily F k) :=
  I.replacementOfRealizable _ (I.native_vertex_realizable F k hk hu hd)

def nativeCompile (F : SignatureFamily AlgebraicComplex)
    (k : ℕ) (hk : 3 ≤ k) (hu : I.Uses (sourceFamily F))
    (hd : I.DegreeDivisible k) : Network AlgebraicComplex 0 :=
  I.compile (I.nativeReplacement F k hk hu hd)

theorem nativeCompile_uses (F : SignatureFamily AlgebraicComplex)
    (k : ℕ) (hk : 3 ≤ k) (hu : I.Uses (sourceFamily F))
    (hd : I.DegreeDivisible k) :
    (I.nativeCompile F k hk hu hd).Uses (targetFamily F k) :=
  I.compile_uses _

theorem nativeCompile_nativeX (F : SignatureFamily AlgebraicComplex)
    (k : ℕ) (hk : 3 ≤ k) (hu : I.Uses (sourceFamily F))
    (hd : I.DegreeDivisible k) : (I.nativeCompile F k hk hu hd).NativeX :=
  I.compile_nativeX _

theorem nativeCompile_partition (F : SignatureFamily AlgebraicComplex)
    (k : ℕ) (hk : 3 ≤ k) (hu : I.Uses (sourceFamily F))
    (hd : I.DegreeDivisible k) :
    (I.nativeCompile F k hk hu hd).denote Fin.elim0 = I.partition :=
  I.compile_partition _

end Instance
end
end Paper2.DegreeCSP
