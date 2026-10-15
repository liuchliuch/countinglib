import ComplexCSP.Complexity.ProjectedClosure

/-! # Exact list-order agreement of the fixed-projection closure machine -/
namespace ComplexCSP.ComplexityProjectedClosure
open MaltsevWitness MaltsevRelations ComplexityWitnessEncoding
variable {d n r : ℕ}

def scopeWord (ρ : Fin r → Fin n) : List ℕ := List.ofFn (fun i => (ρ i).val)
def keyWord (a : Fin r → Fin d) : List ℕ := List.ofFn (fun i => (a i).val)

theorem keyWord_injective : Function.Injective (@keyWord d r) := by
  intro a b h
  have h' : (fun i => (a i).val) = (fun i => (b i).val) := List.ofFn_inj.mp h
  funext i
  exact Fin.ext (congrFun h' i)

theorem project_word (ρ : Fin r → Fin n) (x : Tuple (Fin d) n) :
    project (scopeWord ρ) (word x) = keyWord (projectionKey ρ x) := by
  simp only [project,scopeWord,List.map_ofFn,keyWord]
  congr 1
  funext i
  exact word_getD x (ρ i)

private theorem compress_map {A A' B B' : Type} [DecidableEq B] [DecidableEq B']
    (key : A → B) (key' : A' → B') (f : A → A') (g : B → B')
    (hg : Function.Injective g) (hkey : ∀ a, key' (f a) = g (key a)) (xs : List A) :
    MaltsevWitness.compress key' (xs.map f) = (MaltsevWitness.compress key xs).map f := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.map_cons,MaltsevWitness.compress,ih,List.map_map,Function.comp_def,hkey]
    have ht : ((MaltsevWitness.compress key xs).map (fun a => g (key a))).contains (g (key a)) =
        ((MaltsevWitness.compress key xs).map key).contains (key a) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.contains_iff_mem,List.mem_map]
      constructor
      · rintro ⟨b,hb,he⟩
        exact ⟨b,hb,hg he⟩
      · rintro ⟨b,hb,he⟩
        exact ⟨b,hb,congrArg g he⟩
    rw [ht]
    split <;> rfl

theorem compressRows_word (ρ : Fin r → Fin n) (xs : List (Tuple (Fin d) n)) :
    compressRows (scopeWord ρ) (xs.map word) =
      (MaltsevWitness.compress (projectionKey ρ) xs).map word := by
  rw [compressRows_eq]
  exact compress_map (projectionKey ρ) (project (scopeWord ρ)) word keyWord keyWord_injective
    (project_word ρ) xs

theorem tripleRows_word (m : Operation (Fin d)) (xs : List (Tuple (Fin d) n)) :
    tripleRows d (fun a b c => m (a,b,c)) (xs.map word) =
      (MaltsevWitness.tripleRows m xs).map word := by
  simp only [tripleRows,MaltsevWitness.tripleRows,List.flatMap_map,List.map_flatMap,List.map_map,
    Function.comp_def,mapOperation_word]

theorem closureStep_word (m : Operation (Fin d)) (ρ : Fin r → Fin n)
    (xs : List (Tuple (Fin d) n)) :
    closureStep d (fun a b c => m (a,b,c)) (scopeWord ρ) (xs.map word) =
      (MaltsevWitness.closureStep m ρ xs).map word := by
  rw [closureStep,tripleRows_word,← List.map_append,compressRows_word]
  rfl

theorem keys_word (ρ : Fin r → Fin n) (xs : List (Tuple (Fin d) n)) :
    keys (scopeWord ρ) (xs.map word) = (xs.map (projectionKey ρ)).map keyWord := by
  simp only [keys,List.map_map,Function.comp_def,project_word]

theorem sameKeys_word (ρ : Fin r → Fin n) (xs ys : List (Tuple (Fin d) n)) :
    sameKeys (scopeWord ρ) (xs.map word) (ys.map word) = true ↔
      keySet ρ xs = keySet ρ ys := by
  rw [sameKeys_correct,keys_word,keys_word]
  have hmap (zs : List (Fin r → Fin d)) :
      (zs.map keyWord).toFinset = zs.toFinset.image keyWord := by
    ext a
    simp
  rw [hmap,hmap]
  exact Finset.image_injective keyWord_injective |>.eq_iff

theorem saturate_word (m : Operation (Fin d)) (ρ : Fin r → Fin n)
    (fuel : ℕ) (xs : List (Tuple (Fin d) n)) :
    saturate d (fun a b c => m (a,b,c)) (scopeWord ρ) fuel (xs.map word) =
      (MaltsevWitness.saturate m ρ fuel xs).map word := by
  induction fuel generalizing xs with
  | zero => rfl
  | succ fuel ih =>
    rw [saturate,closureStep_word,MaltsevWitness.saturate]
    by_cases h : keySet ρ (MaltsevWitness.closureStep m ρ xs) = keySet ρ xs
    · rw [if_pos ((sameKeys_word ρ _ _).mpr h),if_pos h]
    · rw [if_neg (fun he => h ((sameKeys_word ρ _ _).mp he)),if_neg h]
      exact ih _

/-- Literal representative lists agree, rather than merely their projections
or supports. The closure budget is d^r for this fixed projection arity. -/
theorem projectedClosure_word (m : Operation (Fin d)) (ρ : Fin r → Fin n)
    (xs : List (Tuple (Fin d) n)) :
    projectedClosure d r (fun a b c => m (a,b,c)) (scopeWord ρ) (xs.map word) =
      (MaltsevWitness.projectedClosure m ρ xs).map word := by
  rw [projectedClosure,compressRows_word,saturate_word]
  rfl

end ComplexCSP.ComplexityProjectedClosure
