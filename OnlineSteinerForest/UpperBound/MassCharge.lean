import OnlineSteinerForest.UpperBound.MassEntropy
import Mathlib.Algebra.BigOperators.Field

/-! Weighted lifetime-depth accounting after the maximum-cost merge rule. -/
namespace OnlineSteinerForest.UpperBound

variable {ι : Type*}

theorem sum_lifetime_charges_le (s : Finset ι) (hs : s.Nonempty) (w : ι → ℝ)
    (hw : ∀ i ∈ s, 0 < w i) :
    (∑ i ∈ s, w i * (1 + Real.log ((∑ j ∈ s, w j) / w i) / Real.log 2)) ≤
      (∑ i ∈ s, w i) * (1 + Real.log s.card / Real.log 2) := by
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hwlog := sum_weight_mul_log_ratio_le s hs w hw
  have hdiv := div_le_div_of_nonneg_right hwlog hlog.le
  calc
    _ = (∑ i ∈ s, w i) + (∑ i ∈ s, w i * Real.log ((∑ j ∈ s, w j) / w i)) / Real.log 2 := by
      rw [Finset.sum_div, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ ≤ (∑ i ∈ s, w i) + (∑ i ∈ s, w i) * Real.log s.card / Real.log 2 := add_le_add le_rfl hdiv
    _ = _ := by ring

end OnlineSteinerForest.UpperBound
