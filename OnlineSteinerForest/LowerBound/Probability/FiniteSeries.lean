import OnlineSteinerForest.LowerBound.PatternSeries
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-! The finite shortcut-count sum is dominated by the manuscript's geometric series. -/
namespace OnlineSteinerForest.LowerBound.Probability

variable [OnlineSteinerForest.PathSelection]

open scoped Classical

theorem finite_pattern_series_le (B : ℕ) (ρ : ℝ) (hρ : 0 < ρ) :
    (∑ q : Fin B, runWeight ρ ^ (q.val + 1) * (2 * ρ) ^ q.val) ≤ 1 / (6 * ρ) := by
  have hR := runWeight_nonneg ρ hρ
  have hprod := runWeight_mul_le_quarter ρ (2 * ρ) hρ le_rfl
  have hterm (k : ℕ) : runWeight ρ ^ (k + 1) * (2 * ρ) ^ k =
      runWeight ρ * (runWeight ρ * (2 * ρ)) ^ k := by
    rw [pow_succ, mul_pow]
    ring
  have hs : Summable (fun k : ℕ => runWeight ρ ^ (k + 1) * (2 * ρ) ^ k) := by
    simp_rw [hterm]
    exact (summable_geometric_of_lt_one (mul_nonneg hR (by positivity)) (by linarith)).mul_left _
  calc
    _ = ∑ k ∈ Finset.range B, runWeight ρ ^ (k + 1) * (2 * ρ) ^ k := by
      exact Fin.sum_univ_eq_sum_range (fun k => runWeight ρ ^ (k + 1) * (2 * ρ) ^ k) B
    _ ≤ ∑' k : ℕ, runWeight ρ ^ (k + 1) * (2 * ρ) ^ k :=
      hs.sum_le_tsum _ (fun _ _ => mul_nonneg (pow_nonneg hR _) (by positivity))
    _ ≤ _ := pattern_series_le ρ (2 * ρ) hρ (by positivity) le_rfl

end OnlineSteinerForest.LowerBound.Probability
