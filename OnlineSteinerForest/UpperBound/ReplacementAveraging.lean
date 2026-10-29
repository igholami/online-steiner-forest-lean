import OnlineSteinerForest.Graph.Cost
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! The finite averaging step used to choose replacement centers. -/
namespace OnlineSteinerForest.UpperBound

/-- A normalized nonnegative weighted average cannot be smaller than every value. -/
theorem exists_le_weighted_bound {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (weight f : Ω → ℝ) (hweight : ∀ x, 0 ≤ weight x) (hnorm : ∑ x, weight x = 1)
    (C : ℝ) (hmean : ∑ x, weight x * f x ≤ C) : ∃ x, f x ≤ C := by
  classical
  obtain ⟨x, _, hmin⟩ := Finset.univ.exists_min_image f Finset.univ_nonempty
  refine ⟨x, ?_⟩
  calc
    f x = ∑ y, weight y * f x := by rw [← Finset.sum_mul, hnorm, one_mul]
    _ ≤ ∑ y, weight y * f y :=
      Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hmin y (Finset.mem_univ _)) (hweight y))
    _ ≤ _ := hmean

end OnlineSteinerForest.UpperBound
