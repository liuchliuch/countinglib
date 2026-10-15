import Paper2.BellReduction.RawCharge

/-! Bell elimination identities directly in the original raw edge-choice sum.
They do not presume that puncturing designated vertices leaves an ordinary
open graph. Thus self-loops and edges between the punctures are included. -/
namespace Paper2.BellReduction.RawBell
open Complexity NativeSmoothing NativeSmoothing.Surgery Choice RawCharge Bell
variable {K : Type} [Field K]

 theorem weight_tables (T U : Table K) (rows : List RawVertex) (c : ℕ → Bool)
    (h : ∀ row ∈ rows, ∀ xs, T row.1 xs = U row.1 xs) :
    Choice.weight T c rows = Choice.weight U c rows := by
  unfold Choice.weight
  congr 1
  apply List.map_congr_left
  intro row hr
  exact h row hr _

 theorem four_charge_eo (a b c d : Bool)
    (h : (8 : ℤ) ∣ listCharge [a,b,c,d]) :
    a.toNat + b.toNat + c.toNat + d.toNat = 2 := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    norm_num [listCharge,bitCharge] at *

 theorem two_charge_unequal (a b : Bool)
    (h : (8 : ℤ) ∣ listCharge [a,b]) : a ≠ b := by
  cases a <;> cases b <;> norm_num [listCharge,bitCharge] at *

/-- A two-Y record is the difference of two literally re-paired X records. -/
theorem two_y (T U : Table K) (m label : ℕ) (p q r s : RawEndpoint)
    (rows : List RawVertex)
    (hT : ∀ a b, T label [a,b] = Y a b)
    (hU : ∀ a b, U label [a,b] = X a b)
    (hrest : ∀ row ∈ rows, ∀ xs, T row.1 xs = U row.1 xs) :
    evaluate T m ((label,[p,q])::(label,[r,s])::rows) =
      evaluate U m ((label,[p,s])::(label,[q,r])::rows) -
      evaluate U m ((label,[p,r])::(label,[q,s])::rows) := by
  unfold evaluate
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  simp only [weight_cons,rowValue,List.map_cons,List.map_nil,hT,hU]
  rw [weight_tables T U rows (extend c) hrest]
  rw [show Y (bit (extend c) p) (bit (extend c) q) *
      (Y (bit (extend c) r) (bit (extend c) s) * Choice.weight U (extend c) rows) =
      (Y (bit (extend c) p) (bit (extend c) q) *
        Y (bit (extend c) r) (bit (extend c) s)) * Choice.weight U (extend c) rows by ring,
    y_square_closures]
  ring

/-- Three raw closure queries remove two I vertices; the EO restriction is
derived term by term from original endpoint incidence and supported charge. -/
theorem two_i (T U : Table K) (m label : ℕ) (p q r s : RawEndpoint)
    (rows : List RawVertex)
    (hp : ([p,q,r,s] ++ (rows.map Prod.snd).flatten).Perm (edgeEnds 0 m))
    (hT : ∀ a b, T label [a,b] = I a b)
    (hU : ∀ a b, U label [a,b] = X a b)
    (hrest : ∀ row ∈ rows, ∀ xs, T row.1 xs = U row.1 xs)
    (hcharge : ∀ row ∈ rows, ∀ xs, T row.1 xs ≠ 0 → (8 : ℤ) ∣ listCharge xs) :
    (2 : K) * evaluate T m ((label,[p,q])::(label,[r,s])::rows) =
      evaluate U m ((label,[p,r])::(label,[q,s])::rows) +
      evaluate U m ((label,[p,s])::(label,[q,r])::rows) -
      evaluate U m ((label,[p,q])::(label,[r,s])::rows) := by
  unfold evaluate
  rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro c _
  simp only [weight_cons,rowValue,List.map_cons,List.map_nil,hT,hU]
  have hw := weight_tables T U rows (extend c) hrest
  rw [← hw]
  by_cases hz : Choice.weight T (extend c) rows = 0
  · rw [hz]
    ring
  · have hc := boundary_charge T m [p,q,r,s] rows (extend c) hp
      (fun row hr => hcharge row hr _) hz
    simp only [List.map_cons,List.map_nil] at hc
    have he := equality_eo_closures (K := K) _ _ _ _ (four_charge_eo _ _ _ _ hc)
    linear_combination he * Choice.weight T (extend c) rows

/-- A single I occurrence vanishes, including a marked self-loop. -/
theorem one_i (T : Table K) (m label : ℕ) (p q : RawEndpoint)
    (rows : List RawVertex)
    (hp : ([p,q] ++ (rows.map Prod.snd).flatten).Perm (edgeEnds 0 m))
    (hT : ∀ a b, T label [a,b] = I a b)
    (hcharge : ∀ row ∈ rows, ∀ xs, T row.1 xs ≠ 0 → (8 : ℤ) ∣ listCharge xs) :
    evaluate T m ((label,[p,q])::rows) = 0 := by
  unfold evaluate
  apply Finset.sum_eq_zero
  intro c _
  rw [weight_cons]
  by_cases hz : Choice.weight T (extend c) rows = 0
  · rw [hz,mul_zero]
  · have hc := boundary_charge T m [p,q] rows (extend c) hp
      (fun row hr => hcharge row hr _) hz
    simp only [List.map_cons,List.map_nil] at hc
    have he := two_charge_unequal _ _ hc
    simp only [rowValue,List.map_cons,List.map_nil,hT]
    have hi : I (K := K) (bit (extend c) p) (bit (extend c) q) = 0 := by
      cases h1 : bit (extend c) p <;> cases h2 : bit (extend c) q <;>
        simp_all [I,ordered,sign]
    rw [hi,zero_mul]

end Paper2.BellReduction.RawBell
