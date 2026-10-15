import Counting.Algorithm.VariableEliminationWork.Cost

/-! # Row materialization which preserves every callback observation -/

namespace Counting.Algorithm.VariableEliminationWork

variable {A R : Type}

/-- Call each row reader once, push its value into the actual output array, and
retain the callback work. Existing accumulator contents are shared. -/
def pushRows (reader : A → Observed R) : List A → Array R → Observed (Array R)
  | [], output => ⟨output, {listCases := 1}⟩
  | a :: xs, output =>
      let first := reader a
      let tail := pushRows reader xs (output.push first.value)
      ⟨tail.value, first.work.add (tail.work.add {listCases := 1, arrayPushes := 1})⟩

@[simp] theorem value_pushRows (reader : A → Observed R) (xs : List A) (output : Array R) :
    (pushRows reader xs output).value = output ++ (xs.map (fun a => (reader a).value)).toArray := by
  induction xs generalizing output with
  | nil => simp [pushRows]
  | cons a xs ih =>
      simp only [pushRows, ih, List.map_cons]
      apply Array.toList_inj.mp
      simp

theorem work_pushRows (reader : A → Observed R) (xs : List A) (output : Array R) :
    (pushRows reader xs output).work =
      (Work.sum (xs.map (fun a => (reader a).work))).add
        {listCases := xs.length + 1, arrayPushes := xs.length} := by
  induction xs generalizing output with
  | nil => simp [pushRows, Work.sum]
  | cons a xs ih =>
      simp only [pushRows, ih, List.map_cons, Work.sum, List.length_cons, Work.add_assoc]
      congr 1

/-- The returned array is the one constructed by `pushRows`, starting from one
empty array. Array push counts are logical operations, not capacity growth bytes. -/
def materialize (reader : A → Observed R) (xs : List A) : Observed (Array R) :=
  let result := pushRows reader xs #[]
  ⟨result.value, result.work.add {arrayConstructions := 1}⟩

@[simp] theorem value_materialize (reader : A → Observed R) (xs : List A) :
    (materialize reader xs).value = (xs.map (fun a => (reader a).value)).toArray := by
  simp [materialize]

theorem work_materialize (reader : A → Observed R) (xs : List A) :
    (materialize reader xs).work =
      (Work.sum (xs.map (fun a => (reader a).work))).add
        {listCases := xs.length + 1, arrayPushes := xs.length, arrayConstructions := 1} := by
  simp only [materialize, work_pushRows, Work.add_assoc]
  rfl

end Counting.Algorithm.VariableEliminationWork
