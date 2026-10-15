import ComplexCSP.Algebra.LegalPurificationTables
import ComplexCSP.Complexity.ProductReplacement

/-! # Actual product collision preservation by legal purification

The proof maps concrete words through the ambient subgroup and the constructed
purification homomorphism. No computable product-class map is supplied.
-/
noncomputable section
open Classical
namespace ComplexCSP.PurificationProductCompatibility
open PlanarHom GeneratingSet

/-- A genuine multiplicative lift transfers arbitrary word-product equalities. -/
theorem compatible_of_lift {I Γ K : Type} [CommMonoid Γ] [Field K]
    (source target : Γ →* K) (hs : Function.Injective source) (lift : I → Γ)
    (A B : I → K) (hA : ∀ i,A i≠0 → source (lift i)=A i)
    (hB : ∀ i,A i≠0 → target (lift i)=B i) : ProductCompatibility.Compatible A B := by
  intro xs ys _ hxs hys he
  have hw (zs : List I) (hzs : ∀ i∈zs,A i≠0) :
      source ((zs.map lift).prod) = (zs.map A).prod := by
    rw [map_list_prod,List.map_map]
    congr 1
    exact List.map_congr_left (fun i hi => hA i (hzs i hi))
  have ht (zs : List I) (hzs : ∀ i∈zs,A i≠0) :
      target ((zs.map lift).prod) = (zs.map B).prod := by
    rw [map_list_prod,List.map_map]
    congr 1
    exact List.map_congr_left (fun i hi => hB i (hzs i hi))
  have hprod : (xs.map lift).prod=(ys.map lift).prod := hs (by rw [hw xs hxs,hw ys hys,he])
  rw [←ht xs hxs,←ht ys hys,hprod]

variable {X D : Type} {S : Finset ℂˣ}

def entryLift (G : X → D → ℂ) (hG : LegalGeneratingSet.ContainsTable S G)
    (p : X × D) : LegalGeneratingSet.EntryGroup S :=
  if hz : G p.1 p.2=0 then 1 else
    ⟨Units.mk0 (G p.1 p.2) hz,Subgroup.subset_closure (hG p.1 p.2 hz)⟩

/-- All original nonzero product collisions are preserved by the actual legal
purification, including mixed positions and arbitrary multiplicities. -/
theorem legal_compatible (L : LegalGeneratingSet S) (G : X → D → ℂ)
    (hG : LegalGeneratingSet.ContainsTable S G) :
    ProductCompatibility.Compatible (fun p : X × D => G p.1 p.2)
      (fun p => L.purifyTable G hG p.1 p.2) := by
  let source : LegalGeneratingSet.EntryGroup S →* ℂ :=
    (Units.coeHom ℂ).comp (LegalGeneratingSet.EntryGroup S).subtype
  let target : LegalGeneratingSet.EntryGroup S →* ℂ :=
    (Units.coeHom ℂ).comp L.purifiedHom
  have hinj : Function.Injective source := by
    intro a b he
    exact Subtype.ext (Units.ext he)
  apply compatible_of_lift source target hinj (entryLift G hG)
  · intro p hp
    simp [entryLift,hp,source]
  · intro p hp
    rw [L.purifyTable_nonzero G hG p.1 p.2 hp]
    simp [entryLift,hp,target]

/-- A common nonzero table-wide scale preserves equal-length collisions. -/
theorem compatible_scale {I K : Type} [Field K] (A B : I → K)
    (h : ProductCompatibility.Compatible A B) (c : K) :
    ProductCompatibility.Compatible A (fun i => c*B i) := by
  intro xs ys hlen hxs hys he
  have hp (zs : List I) : (zs.map (fun i => c*B i)).prod = c^zs.length*(zs.map B).prod := by
    induction zs with
    | nil => simp
    | cons i zs ih => simp only [List.map_cons,List.prod_cons,List.length_cons,pow_succ,ih]; ring
  rw [hp xs,hp ys,hlen,h xs ys hlen hxs hys he]

/-- Zero preservation is proved from the original legal table construction. -/
theorem legal_zero (L : LegalGeneratingSet S) (G : X → D → ℂ)
    (hG : LegalGeneratingSet.ContainsTable S G) (c : ℂ) :
    ∀ p : X × D,G p.1 p.2=0 → c*L.purifyTable G hG p.1 p.2=0 := by
  intro p hp
  rw [L.purifyTable_zero G hG p.1 p.2 hp,mul_zero]

def withUnit {I K : Type} [One K] (f : I → K) : Option I → K
  | none => 1
  | some i => f i

/-- The total codec's dummy unit entry is included in the same actual group
lift. This is needed by the fixed-alphabet replacement machine. -/
theorem legal_compatible_withUnit (L : LegalGeneratingSet S) (G : X → D → ℂ)
    (hG : LegalGeneratingSet.ContainsTable S G) :
    ProductCompatibility.Compatible
      (withUnit (fun p : X × D => G p.1 p.2))
      (withUnit (fun p => L.purifyTable G hG p.1 p.2)) := by
  let source : LegalGeneratingSet.EntryGroup S →* ℂ :=
    (Units.coeHom ℂ).comp (LegalGeneratingSet.EntryGroup S).subtype
  let target : LegalGeneratingSet.EntryGroup S →* ℂ :=
    (Units.coeHom ℂ).comp L.purifiedHom
  have hinj : Function.Injective source := by
    intro a b he
    exact Subtype.ext (Units.ext he)
  let lift : Option (X × D) → LegalGeneratingSet.EntryGroup S :=
    fun p => p.elim 1 (entryLift G hG)
  apply compatible_of_lift source target hinj lift
  · intro p hp
    cases p with
    | none => simp [lift,withUnit]
    | some p => simp [lift,withUnit,entryLift,source,show G p.1 p.2≠0 from hp]
  · intro p hp
    cases p with
    | none => simp [lift,withUnit]
    | some p =>
      change target (entryLift G hG p)=L.purifyTable G hG p.1 p.2
      rw [L.purifyTable_nonzero G hG p.1 p.2 hp]
      simp [entryLift,target,show G p.1 p.2≠0 from hp]

/-- Purity implies algebraicity by the actual root-of-unity equation. -/
theorem pureValue_algebraic {z : ℂ} (hz : IsPureValue z) : IsAlgebraic ℚ z := by
  obtain ⟨n,ζ,hζ,rfl⟩ := hz
  obtain ⟨N,hN,hpow⟩ := hζ.exists_pow_eq_one
  have hroot : IsIntegral ℚ ζ := IsIntegral.of_pow hN (by rw [hpow]; exact isIntegral_one)
  have hnat : IsIntegral ℚ (n : ℂ) := by
    simpa using (isIntegral_algebraMap (R:=ℚ) (A:=ℂ) (x:=(n : ℚ)))
  exact (hnat.mul hroot).isAlgebraic

/-- Every printed legal purified entry is algebraic, derived through the actual
positive common normalization rather than assumed as an output property. -/
theorem legal_algebraic (L : LegalGeneratingSet S) (G : X → D → ℂ)
    (hG : LegalGeneratingSet.ContainsTable S G) :
    ∀ x z, IsAlgebraic ℚ (L.purifyTable G hG x z) := by
  obtain ⟨n,hn,hpure⟩ := L.table_exists_pure_normalization G hG
  have hn0 : (n : ℂ)≠0 := by exact_mod_cast ne_of_gt hn
  have hnat : IsAlgebraic ℚ (n : ℂ) := by
    exact IsIntegral.isAlgebraic (by
      simpa using (isIntegral_algebraMap (R:=ℚ) (A:=ℂ) (x:=(n : ℚ))))
  intro x z
  have h := hnat.inv.mul (pureValue_algebraic (hpure x z))
  simpa only [inv_mul_cancel_left₀ hn0] using h

end ComplexCSP.PurificationProductCompatibility
