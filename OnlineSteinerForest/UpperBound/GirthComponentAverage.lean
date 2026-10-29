import OnlineSteinerForest.UpperBound.FinalParameters
import OnlineSteinerForest.Graph.Cost
import Mathlib.Tactic.Linarith

/-! Selecting a positive-rank component by its cost-to-rank ratio. -/
namespace OnlineSteinerForest.UpperBound.Girth

variable {K : Type*} [Fintype K]

theorem exists_positive_rank_ratio (r : K → ℕ) (c : K → ℝ) (hc : ∀ x, 0 ≤ c x)
    (hr : 0 < ∑ x, r x) :
    ∃ x, 0 < r x ∧ (∑ y, (r y : ℝ)) * c x ≤ (∑ y, c y) * r x := by
  classical
  by_contra! hn
  obtain ⟨x, hx, hxr⟩ := Finset.sum_pos_iff.mp hr
  have hR : (0 : ℝ) < ∑ y, (r y : ℝ) := by exact_mod_cast hr
  have hsum : (∑ y, (∑ z, c z) * (r y : ℝ)) < (∑ y, (∑ z, (r z : ℝ)) * c y) := by
    apply Finset.sum_lt_sum
    · intro y _
      by_cases hy : 0 < r y
      · exact (hn y hy).le
      · have hz : r y = 0 := Nat.eq_zero_of_not_pos hy
        simp only [hz, Nat.cast_zero, mul_zero]
        exact mul_nonneg hR.le (hc y)
    · exact ⟨x, hx, hn x hxr⟩
  simp only [← Finset.mul_sum] at hsum
  nlinarith

theorem cycleFactor_mono {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) : cycleFactor m ≤ cycleFactor n := by
  apply Nat.add_le_add_right
  apply Nat.ceil_mono
  apply Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) (by positivity)
  exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hmn) (by norm_num)

end OnlineSteinerForest.UpperBound.Girth
