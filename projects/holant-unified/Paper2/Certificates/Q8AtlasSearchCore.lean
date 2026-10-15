import Paper2.Certificates.Q8MatchingData
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.SplitIfs

/-! A proof-producing finite search certificate for actual deletion-and-splice
matching constraints. Rejected branches carry an incompatible chosen card;
accepted branches explicitly extend the partial deck. -/
namespace Paper2.Certificates.Q8.Atlas

def DisjointDeleted (d e : PairIndex) : Prop :=
  (deleted d).1 ≠ (deleted e).1 ∧ (deleted d).1 ≠ (deleted e).2 ∧
  (deleted d).2 ≠ (deleted e).1 ∧ (deleted d).2 ≠ (deleted e).2

instance (d e : PairIndex) : Decidable (DisjointDeleted d e) :=
  inferInstanceAs (Decidable ((deleted d).1 ≠ (deleted e).1 ∧ (deleted d).1 ≠ (deleted e).2 ∧
    (deleted d).2 ≠ (deleted e).1 ∧ (deleted d).2 ≠ (deleted e).2))

/-- Deleting a matched edge fixes its endpoints. Otherwise their two mates
are spliced. The other endpoints retain their original mates. -/
def spliceMate (m : Port → Port) (e : PairIndex) (v : Port) : Port :=
  if v = (deleted e).1 ∨ v = (deleted e).2 then v
  else if m v = (deleted e).1 then m (deleted e).2
  else if m v = (deleted e).2 then m (deleted e).1
  else m v

def Compatible (d : PairIndex) (k : Choice) (e : PairIndex) (l : Choice) : Prop :=
  DisjointDeleted d e → spliceMate (fullMate d k) e = spliceMate (fullMate e l) d

instance (d : PairIndex) (k : Choice) (e : PairIndex) (l : Choice) :
    Decidable (Compatible d k e l) := inferInstanceAs (Decidable
      (DisjointDeleted d e → spliceMate (fullMate d k) e = spliceMate (fullMate e l) d))

abbrev Deck := PairIndex → Choice

def DeckCompatible (f : Deck) : Prop := ∀ d e, Compatible d (f d) e (f e)

structure SearchNode (n leaves : ℕ) where
  assigned : PairIndex → Option Choice
  leaf : Option (Fin leaves)
  pivot : PairIndex
  next : Choice → Option (Fin n)
  blocked : Choice → PairIndex

def Agrees {n leaves : ℕ} (f : Deck) (s : SearchNode n leaves) : Prop :=
  ∀ d k, s.assigned d = some k → f d = k

def EdgeValid {n leaves : ℕ} (nodes : Fin n → SearchNode n leaves)
    (i : Fin n) (k : Choice) : Prop :=
  match (nodes i).next k with
  | some j => i.val < j.val ∧ ∀ d, (nodes j).assigned d =
      if d = (nodes i).pivot then some k else (nodes i).assigned d
  | none => ∃ l, (nodes i).assigned ((nodes i).blocked k) = some l ∧
      ¬Compatible (nodes i).pivot k ((nodes i).blocked k) l

instance {n leaves : ℕ} (nodes : Fin n → SearchNode n leaves) (i : Fin n) (k : Choice) :
    Decidable (EdgeValid nodes i k) := by
  unfold EdgeValid
  cases (nodes i).next k <;> infer_instance

def NodeValid {n leaves : ℕ} (rows : Fin leaves → Deck)
    (nodes : Fin n → SearchNode n leaves) (i : Fin n) : Prop :=
  match (nodes i).leaf with
  | some r => ∀ d, (nodes i).assigned d = some (rows r d)
  | none => ∀ k, EdgeValid nodes i k

instance {n leaves : ℕ} (rows : Fin leaves → Deck) (nodes : Fin n → SearchNode n leaves)
    (i : Fin n) : Decidable (NodeValid rows nodes i) := by
  unfold NodeValid
  cases (nodes i).leaf <;> infer_instance

/-- Kernel-checked local certificates imply exhaustive coverage of every
compatible deck extending the starting node. -/
theorem covered_by_valid_tree {n leaves : ℕ} (rows : Fin leaves → Deck)
    (nodes : Fin n → SearchNode n leaves) (valid : ∀ i, NodeValid rows nodes i)
    (f : Deck) (hf : DeckCompatible f) (root : Fin n) (hroot : Agrees f (nodes root)) :
    ∃ r, f = rows r := by
  have all : ∀ h : ℕ, ∀ i : Fin n, n - i.val = h → Agrees f (nodes i) → ∃ r, f = rows r := by
    intro h
    induction h using Nat.strong_induction_on with
    | h h ih =>
      intro i hheight hagree
      have hv := valid i
      cases hl : (nodes i).leaf with
      | some r =>
        have hleaf : ∀ d, (nodes i).assigned d = some (rows r d) := by
          simpa only [NodeValid,EdgeValid,hl] using hv
        refine ⟨r,funext ?_⟩
        intro d
        exact hagree d (rows r d) (hleaf d)
      | none =>
        have hb : ∀ k, match (nodes i).next k with
          | some j => i.val < j.val ∧ ∀ d, (nodes j).assigned d =
              if d = (nodes i).pivot then some k else (nodes i).assigned d
          | none => ∃ l, (nodes i).assigned ((nodes i).blocked k) = some l ∧
              ¬Compatible (nodes i).pivot k ((nodes i).blocked k) l := by
            simpa only [NodeValid,EdgeValid,hl] using hv
        let k := f (nodes i).pivot
        have hk := hb k
        cases hn : (nodes i).next k with
        | none =>
          rw [hn] at hk
          obtain ⟨l,hl,hbad⟩ := hk
          have he := hagree _ _ hl
          exact False.elim (hbad (by simpa only [← he] using hf (nodes i).pivot ((nodes i).blocked k)))
        | some j =>
          rw [hn] at hk
          have hlt : n - j.val < h := by omega
          apply ih (n-j.val) hlt j rfl
          intro d l hd
          rw [hk.2 d] at hd
          by_cases hp : d = (nodes i).pivot
          · rw [if_pos hp] at hd
            have hkl : k = l := Option.some.inj hd
            rw [hp]
            exact hkl
          · rw [if_neg hp] at hd
            exact hagree d l hd
  exact all (n-root.val) root rfl hroot

end Paper2.Certificates.Q8.Atlas
