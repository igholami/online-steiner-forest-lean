import Mathlib.Data.Finset.Sort
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-! Finite cyclic packing from increasing positions on a walk. -/
namespace OnlineSteinerForest.UpperBound

variable {α : Type*}

theorem pairwise_spacing_bound (F : α → ℝ) (r : ℝ) (a : α) (xs : List α)
    (h : (a :: xs).Pairwise (fun x y => F x + r ≤ F y)) :
    (xs.length : ℝ) * r ≤ F (xs.getLastD a) - F a := by
  induction xs generalizing a with
  | nil => simp
  | cons b xs ih =>
    have hab := (List.pairwise_cons.mp h).1 b (by simp)
    have ht := ih b (List.pairwise_cons.mp h).2
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one, List.getLastD_cons]
    linarith

theorem lastD_mem_of_ne_nil (a : α) (xs : List α) (h : xs ≠ []) : xs.getLastD a ∈ xs := by
  cases xs with
  | nil => exact (h rfl).elim
  | cons b xs => simpa only [List.getLastD_cons] using (List.getLastD_mem_cons (l := xs) (a := b))

end OnlineSteinerForest.UpperBound
